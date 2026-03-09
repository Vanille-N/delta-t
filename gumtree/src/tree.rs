use std::cmp;
use std::hash::{Hash, Hasher};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Node<L> {
    label: L,
    height: usize,
    children: Vec<Node<L>>,
    hash: u64,
}

pub mod builders {
    use super::Node;
    use std::hash::{DefaultHasher, Hash, Hasher};

    pub fn leaf<L: Hash>(label: L) -> Node<L> {
        let mut s = DefaultHasher::new();
        label.hash(&mut s);
        Node {
            label,
            height: 1,
            children: Vec::new(),
            hash: s.finish(),
        }
    }

    pub fn node<L: Hash, I>(label: L, children: I) -> Node<L>
    where
        I: IntoIterator<Item = Node<L>>,
    {
        let children = children.into_iter().collect::<Vec<_>>();
        let mut s = DefaultHasher::new();
        label.hash(&mut s);
        let mut height = 1;
        for child in &children {
            child.hash.hash(&mut s);
            height = height.max(child.height + 1)
        }
        Node {
            label,
            height,
            children,
            hash: s.finish(),
        }
    }

    #[derive(Debug)]
    pub enum Ops<L> {
        Open(L),
        Close,
        Leaf(L),
    }

    pub use Ops::*;

    pub fn from_flat<L: Hash + std::fmt::Debug, I>(ops: I) -> Node<L>
        where I: IntoIterator<Item = Ops<L>>
    {
        #[derive(Debug)]
        enum Partial<F, C> {
            Fragment(F),
            Complete(C),
        }

        let mut stack = Vec::new();
        for op in ops.into_iter() {
            match op {
                Open(l) => stack.push(Partial::Fragment(l)),
                Leaf(l) => stack.push(Partial::Complete(leaf(l))),
                Close => {
                    let mut children = Vec::new();
                    loop {
                        if let Some(v) = stack.pop() {
                            match v {
                                Partial::Complete(v) => children.push(v),
                                Partial::Fragment(v) => {
                                    let n = node(v, children.into_iter().rev());
                                    stack.push(Partial::Complete(n));
                                    break
                                },
                            }
                        } else {
                            panic!("Too many closing delimiters")
                        }

                    }
                },
            }
        }
        let Some(fin) = stack.pop() else {
            panic!("No value computed")
        };
        let None = stack.pop() else {
            panic!("Unclosed delimiters")
        };
        let Partial::Complete(n) = fin else {
            panic!("Unclosed delimiters")
        };
        n
    }
}

impl<L: PartialEq + Eq> Node<L> {
    fn isomorphic_zip_aux<'a>(&'a self, other: &'a Self, pairs: &mut Vec<(Ptr<'a, L>, Ptr<'a, L>)>) -> bool {
        if self.hash != other.hash ||
           self.label != other.label ||
           self.height != other.height ||
           self.children.len() != other.children.len() {
               return false;
        }
        for (l, r) in self.children.iter().zip(other.children.iter()) {
            if !l.isomorphic_zip_aux(r, pairs) {
                return false;
            }
        }
        pairs.push((self.as_ptr(), other.as_ptr()));
        true
    }

    pub fn isomorphic_zip<'a>(&'a self, other: &'a Self) -> Option<Vec<(Ptr<'a, L>, Ptr<'a, L>)>> {
        let mut pairs = Vec::new();
        if self.isomorphic_zip_aux(other, &mut pairs) {
            Some(pairs)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct Ptr<'a, L> {
    node: &'a Node<L>,
    addr: usize,
}

impl<'a, L> Clone for Ptr<'a, L> {
    fn clone(&self) -> Self {
        Self {
            node: self.node,
            addr: self.addr,
        }
    }
}

impl<'a, L> Copy for Ptr<'a, L> {}

impl<L> Node<L> {
    pub fn as_ptr(&self) -> Ptr<'_, L> {
        Ptr {
            node: self,
            addr: self as *const Node<L> as usize,
        }
    }
}

impl<'a, L> Ptr<'a, L> {
    pub fn height(self) -> usize {
        self.node.height
    }

    pub fn children(self) -> impl Iterator<Item=Self> {
        self.node.children.iter().map(|n| n.as_ptr())
    }

    pub fn isomorphic_zip(self, other: Self) -> Option<Vec<(Self, Self)>>
    where L: PartialEq + Eq {
        self.node.isomorphic_zip(other.node)
    }
}

impl<'a, L> PartialEq for Ptr<'a, L> {
    fn eq(&self, other: &Self) -> bool {
        self.addr == other.addr
    }
}

impl<'a, L> Eq for Ptr<'a, L> {}

impl<'a, L> Hash for Ptr<'a, L> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.addr.hash(h)
    }
}

impl<'a, L> Ord for Ptr<'a, L> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.node.height.cmp(&other.node.height)
            .then(self.addr.cmp(&other.addr))
    }
}

impl<'a, L> PartialOrd for Ptr<'a, L> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

pub struct Aux<'a, L> {
    parent: HashMap<Ptr<'a, L>, Ptr<'a, L>>,
    iso_candidates: HashMap<u64, Vec<Ptr<'a, L>>>,
}

impl<'a, L> Aux<'a, L> {
    fn empty() -> Self {
        Self {
            parent: HashMap::new(),
            iso_candidates: HashMap::new(),
        }
    }

    fn traverse(&mut self, ptr: Ptr<'a, L>) {
        for child in ptr.children() {
            self.parent.insert(child, ptr);
            self.traverse(child);
        }
        self.iso_candidates.entry(ptr.node.hash).or_insert_with(|| Vec::new()).push(ptr);
    }

    pub fn from(ptr: Ptr<'a, L>) -> Self {
        let mut aux = Self::empty();
        aux.traverse(ptr);
        aux
    }

    pub fn parent(&self, ptr: Ptr<'a, L>) -> Option<Ptr<'a, L>> {
        self.parent.get(&ptr).copied()
    }

    pub fn iso_nonunique(&self, t: Ptr<'a, L>) -> bool
    where L: PartialEq + Eq {
        let candidates = self.iso_candidates.get(&t.node.hash).unwrap();
        if candidates.len() <= 1 {
            return false;
        }
        let mut nb_iso = 0;
        for &candidate in candidates {
            if t.isomorphic_zip(candidate).is_some() {
                nb_iso += 1;
            }
        }
        nb_iso >= 2
    }
}


#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    fn test_iso() {
        let t1 = {
            use builders::*;
            node(1, [
                node(2, [
                    leaf(3),
                    leaf(4),
                    node(1, [
                        leaf(6),
                    ]),
                ]),
                node(2, [
                    node(3, [
                        leaf(5),
                        leaf(5),
                    ]),
                ]),
            ])
        };
        #[rustfmt::skip]
        let t2 = {
            use builders::*;
            node(1, [
                leaf(3),
                leaf(4),
            ])
        };
        assert!(t1.isomorphic_zip(&t1).is_some());
        assert!(t2.isomorphic_zip(&t2).is_some());
        assert!(t1.isomorphic_zip(&t2).is_none());
    }

    #[test]
    fn example_1() {
        let _t1 = {
            use builders::*;
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
    }
}
