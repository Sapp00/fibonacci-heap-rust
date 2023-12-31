mod format;

use std::collections::HashMap;
use std::cell::{Ref, RefCell};
use std::rc::{Rc, Weak};
use format::Min;

pub struct Heap<K: PartialOrd + std::fmt::Display + Min + Copy, V: Copy + std::fmt::Display> {
    n: usize,
    rank: usize,
    trees: usize,
    marks: i32,
    min: Option<Rc<Node<K,V>>>,
}

impl<K: std::fmt::Display + PartialOrd + Min + Copy,V: Copy + std::fmt::Display> Heap<K,V> {
    pub fn new() -> Self {
        Heap {
            n: 0,
            rank: 0,
            trees: 0,
            marks: 0,
            min: None,
        }
    }

    fn get_min(&self) -> Option<Rc<Node<K,V>>> {
        Node::from_borrowed_option_rc(&self.min)
    }

    pub fn insert(&mut self, key: K, value: V) -> Weak<Node<K,V>> {
        self.n += 1;
        self.trees += 1;

        let tmp_node = Node::new(key, value);
        let ret_node = Rc::downgrade(&tmp_node);

        self.min = if let Some(ref min) = self.min {
            Node::concatenate(Rc::clone(min), Rc::clone(&tmp_node));

            if tmp_node.get_key() < min.get_key() {
                Some(tmp_node)
            } else {
                Some(Rc::clone(min))
            }
        } else {
            Some(tmp_node)
        };

        ret_node
    }

    pub fn delete_min(&mut self) {
        if let Some(min) = self.get_min() {
            self.n -= 1;
            self.trees -= 1;
            self.trees += min.get_rank();

            let left = min.get_left().unwrap();
            let child = min.get_child();

            Node::remove(Rc::clone(&min));
            min.clear_child();
            min.clear_left();

            self.min = if let Some(child) = child {
                if !Rc::ptr_eq(&left, &min) {
                    Node::concatenate(left, Rc::clone(&child));
                }

                Some(Node::find_min(child))
            } else {
                if !Rc::ptr_eq(&left, &min) {
                    Some(Node::find_min(left))
                } else {
                    None
                }
            };
        }

        if let Some(min) = self.get_min() {
            let mut nc = NodeConsolidator::new(self.trees);
            nc.consolidate(min);
            self.trees = nc.trees;
            self.rank = nc.rank;
        }
    }

    pub fn print(&self) {
        if let Some(min) = self.get_min() {
            for node in NodeIterator::new(min) {
                node.print(0);
            }
        }
    }

    // set the Key of the Node {node} to {key}.
    pub fn reduce_key(&mut self, node: Rc<Node<K,V>>, key: K) {
        if key < node.get_key() {
            node.set_key(key);

            if let Some(parent) = node.get_parent() {
                if parent.get_key() < node.get_key() {
                    return;
                }
            }

            // order has changed
            let root = self.get_min().unwrap();

            if node.get_key() < root.get_key() {
                self.min = Some(Rc::clone(&node));
            }

            self.prune(node, root);

        }
    }

    pub fn delete(&mut self, node: Rc<Node<K,V>>) {
        self.reduce_key(node, K::min_value());
        self.delete_min();
    }

    pub fn union(&mut self, mut heap: Heap<K,V>) {
        if let Some(f_min) = heap.get_min() {
            if let Some(l_min) = self.get_min() {
                if f_min.get_key() < l_min.get_key() {
                    self.min = Some(Rc::clone(&f_min));
                }

                Node::concatenate(l_min, f_min);
            } else {
                self.min = Some(f_min);
            }
            heap.min = None
        }
    }

    fn prune(&mut self, node: Rc<Node<K,V>>, root: Rc<Node<K,V>>) -> Option<()> {
        let parent = node.get_parent()?;
        let child = parent.get_child().unwrap();

        if node.is_marked() {
            node.unmark();
            self.marks -= 1;
        }

        if Rc::ptr_eq(&child, &node) {
            if parent.get_rank() > 1 {
                if let Some(left) = node.get_left() {
                    parent.set_child(left);
                }
            } else {
                parent.clear_child();
            }
        }

        parent.decrement_rank();

        Node::concatenate(Rc::clone(&root), Node::remove(Rc::clone(&node)));
        self.trees += 1;

        if parent.is_marked() {
            self.prune(parent, root);
        } else if parent.get_parent().is_some() {
            self.marks += 1;
            parent.mark();
        }

        Some(())
    }
}

impl<K,V> Drop for Heap<K,V> where K: PartialOrd + std::fmt::Display + Min + Copy, V: Copy + std::fmt::Display {
    fn drop(&mut self) {
        if let Some(min) = self.get_min() {
            for node in NodeIterator::new(min) {
                Node::cleanup(node);
            }
        }
    }
}

pub struct Node<K,V> {
    key: RefCell<K>,
    value: V,
    rank: RefCell<usize>,
    marked: RefCell<bool>,
    left: RefCell<Option<Rc<Node<K,V>>>>,
    right: RefCell<Option<Weak<Node<K,V>>>>,
    parent: RefCell<Option<Weak<Node<K,V>>>>,
    child: RefCell<Option<Rc<Node<K,V>>>>,
}

impl<K: std::fmt::Display + PartialOrd + Min + Copy,V: Copy> Node<K,V> {
    fn new(key: K, value: V) -> Rc<Self> {
        let node = Rc::new(Node {
            key: RefCell::new(key),
            value: value,
            rank: RefCell::new(0),
            marked: RefCell::new(false),
            left: RefCell::new(None),
            right: RefCell::new(None),
            parent: RefCell::new(None),
            child: RefCell::new(None),
        });

        node.set_left(Rc::clone(&node));
        node.set_right(Rc::downgrade(&node));

        node
    }

    pub fn get_value(&self) -> V {
        self.value
    }

    pub fn get_key(&self) -> K {
        *self.key.borrow()
    }

    fn set_key(&self, key: K) {
        *self.key.borrow_mut() = key;
    }

    fn get_rank(&self) -> usize {
        *self.rank.borrow()
    }

    fn is_marked(&self) -> bool {
        *self.marked.borrow()
    }

    fn mark(&self) {
        *self.marked.borrow_mut() = true;
    }

    fn unmark(&self) {
        *self.marked.borrow_mut() = false;
    }

    fn increment_rank(&self) {
        *self.rank.borrow_mut() += 1;
    }

    fn decrement_rank(&self) {
        *self.rank.borrow_mut() -= 1;
    }

    fn print(&self, depth: i32) {
        let mut s = String::new();
        for _ in 0..depth {
            s.push_str("  ");
        }
        if self.is_marked() {
            println!("{}{}*:", s, self.get_key());
        } else {
            println!("{}{}:", s, self.get_key());
        }

        if let Some(child) = self.get_child() {
            for node in NodeIterator::new(child) {
                node.print(depth + 1);
            }
        }
    }

    fn remove(node: Rc<Node<K,V>>) -> Rc<Node<K,V>> {
        let left = node.get_left().unwrap();
        let right = node.get_right().unwrap();

        if !Rc::ptr_eq(&node, &left) {
            left.set_right(Rc::downgrade(&right));
            right.set_left(Rc::clone(&left));
        }

        if let Some(parent) = node.get_parent() {
            if let Some(child) = parent.get_child() {
                if Rc::ptr_eq(&node, &child) {
                    if Rc::ptr_eq(&node, &left) {
                        parent.clear_child();
                    } else {
                        parent.set_child(left);
                    }
                }
            }
        }

        node.set_left(Rc::clone(&node));
        node.set_right(Rc::downgrade(&node));

        node
    }

    fn cleanup(node: Rc<Self>) {
        if let Some(child) = node.get_child() {
            for node in NodeIterator::new(child) {
                Node::cleanup(node);
            }
        }

        node.clear_left();
        node.clear_child();
    }

    fn set_left(&self, node: Rc<Self>) {
        *self.left.borrow_mut() = Some(node);
    }

    fn get_left(&self) -> Option<Rc<Self>> {
        Node::from_ref_option_rc(self.left.borrow())
    }

    fn clear_left(&self) {
        *self.left.borrow_mut() = None;
    }

    fn set_right(&self, node: Weak<Self>) {
        *self.right.borrow_mut() = Some(node);
    }

    fn get_right(&self) -> Option<Rc<Self>> {
        Node::from_ref_option_weak(self.right.borrow())
    }

    fn set_parent(&self, node: Weak<Self>) {
        *self.parent.borrow_mut() = Some(node);
    }

    fn get_parent(&self) -> Option<Rc<Self>> {
        Node::from_ref_option_weak(self.parent.borrow())
    }

    fn set_child(&self, node: Rc<Self>) {
        *self.child.borrow_mut() = Some(node);
    }

    fn get_child(&self) -> Option<Rc<Self>> {
        Node::from_ref_option_rc(self.child.borrow())
    }

    fn clear_child(&self) {
        *self.child.borrow_mut() = None;
    }

    fn from_ref_option_rc(node: Ref<Option<Rc<Self>>>) -> Option<Rc<Self>> {
        if let Some(ref n) = *node {
            Some(Rc::clone(n))
        } else {
            None
        }
    }

    fn from_borrowed_option_rc(node: &Option<Rc<Self>>) -> Option<Rc<Self>> {
        if let &Some(ref n) = node {
            Some(Rc::clone(n))
        } else {
            None
        }
    }

    fn from_ref_option_weak(node: Ref<Option<Weak<Self>>>) -> Option<Rc<Self>> {
        if let Some(ref n) = *node {
            Weak::upgrade(n)
        } else {
            None
        }
    }

    fn concatenate(node1: Rc<Self>, node2: Rc<Self>) {
        let node1_weak = Rc::downgrade(&node1);
        let node1_left = node1.get_left().unwrap();
        let node2_left = node2.get_left().unwrap();

        if let Some(parent) = node2.get_parent() {
            if let Some(child) = parent.get_child() {
                if Rc::ptr_eq(&node2, &child) {
                    parent.clear_child();
                }
            }
        }

        let n1parent = if let Some(ref parent) = *node1.parent.borrow() {
            Some(Weak::clone(parent))
        } else {
            None
        };

        if let Some(parent) = n1parent {
            for node in NodeIterator::new(Rc::clone(&node2)) {
                node.set_parent(Weak::clone(&parent));
            }
        }

        node2_left.set_right(Weak::clone(&node1_weak));
        node1.set_left(Rc::clone(&node2_left));

        node2.set_left(Rc::clone(&node1_left));
        node1_left.set_right(Rc::downgrade(&node2));
    }

    fn find_min(node: Rc<Self>) -> Rc<Self> {
        let mut min_node = Rc::clone(&node);

        for node in NodeIterator::new(node) {
            if node.get_key() < min_node.get_key() {
                min_node = Rc::clone(&node);
            }
        }

        min_node
    }
}

pub struct NodeConsolidator<K,V> {
    trees: usize,
    rank: usize,
    ranks: HashMap<usize, Rc<Node<K,V>>>,
}

impl<K: PartialOrd + Min + std::fmt::Display + Copy, V: Copy> NodeConsolidator<K,V> {
    fn new(trees: usize) -> Self {
        NodeConsolidator {
            trees: trees,
            rank: 0,
            ranks: HashMap::new(),
        }
    }

    fn consolidate(&mut self, node: Rc<Node<K,V>>) {
        if self.ranks.len() == self.trees {
            return;
        }

        let rank = node.get_rank();

        let node2 = Rc::clone(&node);

        let ranked_node = match self.ranks.get(&rank) {
            Some(ref ranked_node) => {
                if !Rc::ptr_eq(&node, ranked_node) {
                    Some(Rc::clone(ranked_node))
                } else {
                    None
                }
            }
            None => None,
        };

        if let Some(ranked_node) = ranked_node {
            let node = if node.get_key() < ranked_node.get_key() {
                self.merge_nodes(node2, ranked_node)
            } else {
                self.merge_nodes(ranked_node, node2)
            };

            self.consolidate(node);
        } else {
            self.ranks.insert(node.get_rank(), Rc::clone(&node));
        }

        if let Some(right) = node.get_right() {
            self.consolidate(right);
        }
    }

    fn merge_nodes(&mut self, lesser_node: Rc<Node<K,V>>, greater_node: Rc<Node<K,V>>) -> Rc<Node<K,V>> {
        self.trees -= 1;

        if let Some(parent) = greater_node.get_parent() {
            parent.decrement_rank();
        }

        let gn2 = Rc::clone(&greater_node);
        Node::remove(gn2);

        if let Some(child) = lesser_node.get_child() {
            Node::concatenate(child, greater_node);
        } else {
            greater_node.set_parent(Rc::downgrade(&lesser_node));
            lesser_node.set_child(greater_node);
        }

        let rank = lesser_node.get_rank();
        self.ranks.remove(&rank);

        lesser_node.increment_rank();

        if lesser_node.get_rank() > self.rank {
            self.rank = lesser_node.get_rank();
        }

        lesser_node
    }
}

pub struct NodeIterator<K,V> {
    first: Rc<Node<K,V>>,
    current: Option<Rc<Node<K,V>>>,
    first_seen: bool,
}

impl<K,V> NodeIterator<K,V> {
    fn new(node: Rc<Node<K,V>>) -> Self {
        NodeIterator {
            first: Rc::clone(&node),
            current: Some(Rc::clone(&node)),
            first_seen: false,
        }
    }
}

impl<K,V> Iterator for NodeIterator<K,V> where K: PartialOrd + Min + std::fmt::Display + Copy, V: Copy {
    type Item = Rc<Node<K,V>>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = Node::from_borrowed_option_rc(&self.current)?;

        if self.first_seen && Rc::ptr_eq(&current, &self.first) {
            return None;
        } else if Rc::ptr_eq(&current, &self.first) {
            self.first_seen = true;
        }

        self.current = current.get_left();

        Some(current)
    }
}

#[cfg(test)]
mod tests {
    use std::{rc::{self, Rc}};

    use crate::Heap;

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn basic_test(){
        let mut heap = Heap::new();
        heap.print();
        let v: Vec<_> = (0..17).map(|i| heap.insert(i, i)).collect();

        for i in 0..17{
            let n = heap.get_min();
            assert_eq!(n.is_some(), true);
            assert_eq!(n.clone().unwrap().value , i, 
                "Min element should be {}, but is {}.", 
                i,
                n.unwrap().value,
            );

            heap.delete_min();
            let n = heap.get_min();
            if n.is_some(){
                assert_ne!(n.clone().unwrap().value , i, 
                    "Min element has been deleted. Should be different to {}, but is {}.", 
                    i,
                    n.unwrap().value,
                );
            }
        }
    }

    #[test]
    fn decrease_test(){
        let mut heap = Heap::new();
        heap.print();
        let v: Vec<_> = (1..17).map(|i| heap.insert(i, i)).collect();

        for i in 1..17{
            let n = heap.get_min();
            assert_eq!(n.is_some(), true);
            assert_eq!(i, n.clone().unwrap().get_key(), 
                "Min element should be {}, but is {}.", 
                i,
                n.clone().unwrap().get_key(),
            );

            //println!("old key: {} ", n.clone().unwrap().get_key());

            heap.reduce_key( n.clone().unwrap(), i-1);

            //let n = heap.get_min();
            //println!("new key: {} ", n.unwrap().get_key());

            //  the min should be one less now.
            let n = heap.get_min();
            assert_eq!(n.is_some(), true);
            assert_eq!(i-1, n.clone().unwrap().get_key(), 
                "Min element should be one less now. Should be {}, but is {}.", 
                i-1,
                n.clone().unwrap().get_key(),
            );

            heap.delete_min();

            let n = heap.get_min();

            if n.is_some(){
                assert_eq!(i+1, n.clone().unwrap().get_key(),
                    "Min element should be again {}, but is {}.", 
                    i+1,
                    n.clone().unwrap().get_key(),
                );
            }
        }
    }

    #[test]
    fn decrease_test2(){
        let mut heap = Heap::new();
        heap.print();
        let v: Vec<_> = (1..17).map(|i| heap.insert(i, i)).collect();

        // length should be one less now
        assert_eq!(heap.n, 16);

        // check initial min
        let ee = heap.get_min();
        assert_eq!(ee.is_some(), true);
        let e = ee.unwrap();
        assert_eq!(e.get_key(), 1);
        assert_eq!(e.get_value(), 1);

        // e should be (2, 2)
        let e = v[2].upgrade().unwrap();
        assert_eq!(e.get_key(), 3);
        assert_eq!(e.get_value(), 3);

        // set e to (0,2)
        heap.reduce_key(e, 0);

    
        // check new min
        let ee = heap.get_min();
        assert_eq!(ee.is_some(), true);
        let e = ee.unwrap();
        assert_eq!(e.get_key(), 0);
        assert_eq!(e.get_value(), 3);

        heap.delete_min();
        // length should be one less now
        assert_eq!(heap.n, 15);

        // check initial min. should be back
        let ee = heap.get_min();
        assert_eq!(ee.is_some(), true);
        let e = ee.unwrap();
        assert_eq!(e.get_key(), 1);
        assert_eq!(e.get_value(), 1);

    }
}
