use std::collections::{HashMap, BinaryHeap, HashSet};
use crate::tree::{Node, Ptr, Aux};

#[derive(Debug)]
pub struct Mapping<'a, L> {
    src_to_dst: HashMap<Ptr<'a, L>, Ptr<'a, L>>,
    dst_to_src: HashMap<Ptr<'a, L>, Ptr<'a, L>>,
}

#[derive(Debug)]
struct List<'a, L> {
    pq: BinaryHeap<Ptr<'a, L>>,
}

impl<'a, L> List<'a, L> {
    fn new() -> Self {
        Self {
            pq: BinaryHeap::new(),
        }
    }

    fn push(&mut self, node: Ptr<'a, L>) {
        self.pq.push(node)
    }

    fn extend(&mut self, node: Ptr<'a, L>) {
        for child in node.children() {
            self.push(child)
        }
    }

    fn peek(&self) -> usize {
        let Some(ptr) = self.pq.peek() else { return 0 };
        ptr.height()
    }

    fn pop(&mut self) -> Vec<Ptr<'a, L>> {
        let current = self.peek();
        if current == 0 {
            return vec![];
        }
        let mut elts = Vec::new();
        while self.peek() == current {
            elts.push(self.pq.pop().unwrap())
        }
        elts
    }
}

impl<'a, L> Mapping<'a, L>
    where L: std::fmt::Debug + PartialEq + Eq
{
    fn empty() -> Self {
        Self {
            src_to_dst: HashMap::new(),
            dst_to_src: HashMap::new(),
        }
    }

    fn assoc(&mut self, src: Ptr<'a, L>, dst: Ptr<'a, L>) {
        self.src_to_dst.insert(src, dst);
        self.dst_to_src.insert(dst, src);
    }

    fn dice_coeff(&self, t1: Ptr<'a, L>, t2: Ptr<'a, L>) -> f64 {
        let s1 = t1.children().into_iter().collect::<HashSet<_>>();
        let s2 = t2.children().into_iter().collect::<HashSet<_>>();
        let mut common = 0;
        for c1 in t1.children() {
            if let Some(c2) = self.src_to_dst.get(&c1) {
                if s2.contains(&c2) {
                    common += 1;
                }
            }
        }
        for c2 in t2.children() {
            if let Some(c1) = self.dst_to_src.get(&c2) {
                if s1.contains(&c1) {
                    common += 1;
                }
            }
        }
        (common as f64) / ((s1.len() + s2.len()) as f64)
    }

    fn top_down_isos(src: Ptr<'a, L>, dst: Ptr<'a, L>, min_height: usize) -> Self {
        let mut mappings = Self::empty();
        let mut candidates = Vec::new();
        let mut mapped_src = HashSet::new();
        let mut mapped_dst = HashSet::new();
        let aux1 = Aux::from(src);
        let aux2 = Aux::from(dst);
        let mut l1 = List::new();
        let mut l2 = List::new();
        l1.push(src);
        l2.push(dst);
        while l1.peek().min(l2.peek()) >= min_height {
            if l1.peek() > l2.peek() {
                for child in l1.pop() {
                    l1.extend(child);
                }
            } else if l1.peek() < l2.peek() {
                for child in l2.pop() {
                    l2.extend(child);
                }
            } else {
                let h1 = l1.pop();
                let h2 = l2.pop();
                for &t1 in &h1 {
                    for &t2 in &h2 {
                        if let Some(pairs) = t1.isomorphic_zip(t2) {
                            if aux2.iso_nonunique(t1) || aux1.iso_nonunique(t2) {
                                println!("Candidate mapping: {:?}, {:?}\n", &t1, &t2);
                                candidates.push((t1, t2));
                                mapped_src.insert(t1);
                                mapped_dst.insert(t2);
                            } else {
                                println!("Definitive mapping: {:?}, {:?}\n", &t1, &t2);
                                for (s1, s2) in pairs {
                                    mappings.assoc(s1, s2);
                                }
                            }
                        }
                    }
                }
                for &t1 in &h1 {
                    if !mapped_src.contains(&t1) && !mappings.src_to_dst.contains_key(&t1) {
                        println!("{:?} is unmapped\n", &t1);
                        l1.extend(t1);
                    }
                }
                for &t2 in &h2 {
                    if !mapped_dst.contains(&t2) && !mappings.dst_to_src.contains_key(&t2) {
                        println!("{:?} is unmapped\n", &t2);
                        l2.extend(t2);
                    }
                }
            }
        }
        let mut candidates = candidates.into_iter().map(|(t1, t2)| {
            let coeff = mappings.dice_coeff(aux1.parent(t1).expect("Can't be the root"), aux2.parent(t2).expect("Can't be the root"));
            (coeff, t1, t2)
        }).collect::<Vec<_>>();
        candidates.sort_by(|a,b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Less));
        while let Some((_, t1, t2)) = candidates.pop() {
            if mappings.src_to_dst.contains_key(&t1) || mappings.dst_to_src.contains_key(&t2) {
                continue;
            }
            let pairs = t1.isomorphic_zip(t2).expect("Candidate mappings are isomorphic");
            for (s1, s2) in pairs {
                mappings.assoc(s1, s2);
            }
        }
        mappings
    }
}

#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    fn example_1() {
        let t1 = {
            use crate::tree::builders::*;
            from_flat([
                Open("CompilationUnit"),
                Open("TypeDeclaration"),
                Leaf("Modifier: public"),
                Leaf("Name: Test"),
                Open("MethodDeclaration"),
                Leaf("Modifier: private"),
                Open("Type: String"),
                Leaf("Name: String"),
                Close,
                Leaf("Name: foo"),
                Open("VariableDecl"),
                Leaf("Type: int"),
                Leaf("Name: i"),
                Close,
                Open("Block"),
                Open("IfStatement"),
                Open("InfixExpr: =="),
                Leaf("Name: i"),
                Leaf("Number: 0"),
                Close,
                Open("ReturnStatement"),
                Leaf("String: Bar"),
                Close,
                Open("IfStatement"),
                Open("InfixExpr: =="),
                Leaf("Name: i"),
                Open("PrefixExpr: -"),
                Leaf("Number: 1"),
                Close,
                Close,
                Open("ReturnStatement"),
                Leaf("String: Foo!"),
                Close,
                Close,
                Close,
                Close,
                Close,
                Close,
                Close,
            ])
        };
        let t2 = {
            use crate::tree::builders::*;
            from_flat([
                Open("CompilationUnit"),
                Open("TypeDeclaration"),
                Leaf("Modifier: public"),
                Leaf("Name: Test"),
                Open("MethodDeclaration"),
                Leaf("Modifier: public"),
                Open("Type: String"),
                Leaf("Name: String"),
                Close,
                Leaf("Naime: foo"),
                Open("VariableDecl"),
                Leaf("Type: int"),
                Leaf("Name: i"),
                Close,
                Open("Block"),
                Open("IfStatement"),
                Open("InfixExpr: =="),
                Leaf("Name: i"),
                Leaf("Number: 0"),
                Close,
                Open("ReturnStatement"),
                Leaf("String: Foo!"),
                Close,
                Close,
                Close,
                Close,
                Close,
                Close,
            ])
        };
        let mappings = Mapping::top_down_isos(t1.as_ptr(), t2.as_ptr(), 2);
        unimplemented!("{:?}", mappings)
    }
}
