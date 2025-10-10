use std::fmt;

use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use crate::error::{Error, Result};

pub mod error;

/// Node of Double Linked List. Node is alias name of the Smartpointer of RefCell Node
pub type Node<T> = Rc<RefCell<VNode<T>>>;

/// Node of Double Linked List.
/// Node hold `Value`, `Next Node`, `Previouse Node`, and `Identifier`
#[derive(Debug)]
pub struct VNode<T> {
    /// Smart pointer of next node. Containt `None` if no next node
    next: Option<Node<T>>,
    /// Smart weak pointer of previouse node. Contain `None` if no previouse node
    prev: Option<Weak<RefCell<VNode<T>>>>,
    /// Value of Node
    val: T,
    /// Key identifier
    identifier: usize,
}

impl<T> VNode<T> {
    /// Set value of Node.
    pub fn set_value(&mut self, value: T) {
        self.val = value;
    }

    /// Get Reference Value of Node
    pub fn get_value_ref(&self) -> &T {
        &self.val
    }
}

/// Double Linked List Object
#[derive(Debug)]
pub struct DoubleLinkedList<T> {
    head: Option<Node<T>>,
    size: usize,
    tail: Option<Node<T>>,
    identifier: usize,
}

impl<T: fmt::Display> fmt::Display for DoubleLinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut cur = self.head.clone();
        let mut first = true;
        while let Some(node) = cur {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}", node.borrow().val)?;
            cur = node.borrow().next.clone();
            first = false;
        }
        write!(f, "]")
    }
}

impl<T> DoubleLinkedList<T> {
    /// Create new Double Linked List object with empty Node. Parameter `id` is unique id of Double Linked List.
    /// Each Double Linked List must have different `id`.
    /// Example:
    /// ```rust
    /// use gix_dll_rlib::DoubleLinkedList;
    ///
    /// let mut dll= DoubleLinkedList::<String>::new(0);
    /// println!("{}",dll);
    /// ```
    pub fn new(id: usize) -> Self {
        Self {
            head: None,
            tail: None,
            size: 0,
            identifier: id,
        }
    }

    /// Get length of Nodes in Double Linked List.
    /// ```rust
    /// use gix_dll_rlib::DoubleLinkedList;
    ///
    /// let mut dll=DoubleLinkedList::new(1);
    /// let one = dll.append("one".to_string());
    ///
    /// assert_eq!(1,dll.length());
    /// ```
    pub fn length(&self) -> usize {
        self.size
    }

    /// Append Node to Double Linked List. This function will add Node to the last or tail of Double Linked List.
    /// This function will return Node. If Double Linked List is empty
    /// head and tail will contain same node that just created.
    /// Example:
    /// ```rust
    /// use gix_dll_rlib::DoubleLinkedList;
    /// use gix_dll_rlib::Node;
    /// use std::{
    /// cell::RefCell,
    /// rc::Rc,
    /// };
    ///
    /// let mut dll=DoubleLinkedList::new(0);
    /// let one:Node<String> = dll.append("one".to_string());
    ///
    /// assert_eq!(one.borrow().get_value_ref(),"one");
    /// ```
    pub fn append(&mut self, value: T) -> Node<T> {
        let node = Rc::new(RefCell::new(VNode {
            next: None,
            prev: self.tail.as_ref().map(|tail| Rc::downgrade(tail)),
            val: value,
            identifier: self.identifier,
        }));

        match self.tail.take() {
            Some(old_tail) => {
                old_tail.borrow_mut().next = Some(node.clone());
                self.tail = Some(node.clone());
            }
            None => {
                // empty: set head and tail
                self.head = Some(node.clone());
                self.tail = Some(node.clone());
            }
        }
        self.size += 1;
        node
    }

    /// Prepend Node to Double Linked List. This function will add Node to the first or head of Double Linked List.
    /// This function will return Smartpointer of RefCell Node. If Double Linked List is empty
    /// head and tail will contain same node that just created.
    /// Example:
    /// ```rust
    /// use gix_dll_rlib::DoubleLinkedList;
    /// use gix_dll_rlib::Node;
    /// use std::{
    /// cell::RefCell,
    /// rc::Rc,
    /// };
    ///
    /// let mut dll=DoubleLinkedList::new(3);
    /// let one:Node<String> = dll.prepend("one".to_string());
    ///
    /// assert_eq!(one.borrow().get_value_ref(),"one");
    /// ```
    pub fn prepend(&mut self, value: T) -> Node<T> {
        let node = Rc::new(RefCell::new(VNode {
            next: self.head.as_ref().map(|head| head.clone()),
            prev: None,
            val: value,
            identifier: self.identifier,
        }));

        match self.head.take() {
            Some(old_head) => {
                old_head.borrow_mut().prev = Some(Rc::downgrade(&node));
                self.head = Some(node.clone());
            }
            None => {
                // empty: set head and tail
                self.head = Some(node.clone());
                self.tail = Some(node.clone());
            }
        }
        self.size += 1;
        node
    }

    pub fn insert_after(&mut self, node: Node<T>, value: T) -> Result<Node<T>> {
        // if empty return error
        if self.size == 0 {
            return Err(Error::Empty);
        }

        // check if list and node is associated
        if self.identifier != node.borrow().identifier {
            return Err(Error::NodeNotAssociated);
        }

        // if node is same as tail just call append function
        if let Some(tail) = &self.tail {
            if Rc::ptr_eq(&node, tail) {
                return Ok(self.append(value));
            }
        }

        //get node next
        let node_next = node.borrow().next.clone();

        // create new node
        let new_node = Rc::new(RefCell::new(VNode {
            next: node_next.clone(),          // set next with node.next
            prev: Some(Rc::downgrade(&node)), // set previouse with node
            val: value,
            identifier: self.identifier,
        }));

        // set node.next previous with new node
        match node_next {
            Some(next_node) => {
                next_node.borrow_mut().prev = Some(Rc::downgrade(&new_node));
            }
            None => {
                return Err(Error::InsertFailed);
            }
        }

        // set node.next with new node
        node.borrow_mut().next = Some(new_node.clone());

        self.size += 1;
        Ok(new_node)
    }

    pub fn insert_before(&mut self, node: Node<T>, value: T) -> Result<Node<T>> {
        // if empty cannot insert before
        if self.size == 0 {
            return Err(Error::Empty);
        }

        // check if list and node is associated
        if self.identifier != node.borrow().identifier {
            return Err(Error::NodeNotAssociated);
        }

        // if node same as head just call prepend function
        if let Some(head) = &self.head {
            if Rc::ptr_eq(&node, head) {
                return Ok(self.prepend(value));
            }
        }

        // get node prev
        let node_prev = node.borrow().prev.clone();

        // create new node
        let new_node = Rc::new(RefCell::new(VNode {
            next: Some(node.clone()),
            prev: node_prev.clone(),
            val: value,
            identifier: self.identifier,
        }));

        // set node.prev next with new node
        match node_prev.ok_or(Error::InsertFailed)?.upgrade() {
            Some(prev_node) => {
                prev_node.borrow_mut().next = Some(new_node.clone());
            }
            None => {
                return Err(Error::InsertFailed);
            }
        }

        // set node.prev with new node
        node.borrow_mut().prev = Some(Rc::downgrade(&new_node));

        self.size += 1;
        Ok(new_node)
    }

    pub fn remove(&mut self, node: Node<T>) -> Result<T>
    where
        T: Default,
    {
        if self.size == 0 {
            return Err(Error::Empty);
        }

        // Update prev and next pointers
        let prev_node = node.borrow().prev.clone();
        let next_node = node.borrow().next.clone();

        // If node is head, update head
        if let Some(head) = &self.head {
            if Rc::ptr_eq(&node, head) {
                self.head = next_node.clone();
            }
        }
        // If node is tail, update tail
        if let Some(tail) = &self.tail {
            if Rc::ptr_eq(&node, tail) {
                self.tail = prev_node.as_ref().and_then(|w| w.upgrade());
            }
        }

        // Update prev.next -> next
        if let Some(prev_weak) = prev_node.as_ref() {
            if let Some(prev_node) = prev_weak.upgrade() {
                prev_node.borrow_mut().next = next_node.clone();
            }
        }
        // Update next.prev -> prev
        if let Some(next_node) = next_node {
            next_node.borrow_mut().prev = prev_node.clone();
        }

        self.size -= 1;
        // Take value out of node safely
        let val = std::mem::take(&mut node.borrow_mut().val);
        Ok(val)
    }

    pub fn remove_at(&mut self, index: usize) -> Result<T>
    where
        T: Default,
    {
        if self.size == 0 {
            return Err(Error::Empty);
        }
        if index >= self.size {
            return Err(Error::IndexOutOfBound);
        }

        let node = match index <= self.size / 2 {
            true => {
                let mut id = 0usize;
                let mut current_node = self.head.clone();
                while id < index {
                    current_node = current_node
                        .ok_or(Error::RemoveFailed)?
                        .borrow()
                        .next
                        .clone();
                    id += 1;
                }
                current_node.ok_or(Error::RemoveFailed)?
            }
            false => {
                let mut id = self.size - 1;
                let mut current_node = self.tail.clone();
                while id > index {
                    current_node = current_node
                        .ok_or(Error::RemoveFailed)?
                        .borrow()
                        .prev
                        .as_ref()
                        .and_then(|w| w.upgrade());
                    id -= 1;
                }
                current_node.ok_or(Error::RemoveFailed)?
            }
        };
        self.remove(node)
    }

    pub fn set_value_at(&mut self, value: T, index: usize) -> Result<()> {
        if self.size == 0 {
            return Err(Error::Empty);
        }
        if index >= self.size {
            return Err(Error::IndexOutOfBound);
        }

        let node = match index <= self.size / 2 {
            true => {
                let mut id = 0usize;
                let mut current_node = self.head.clone();
                while id < index {
                    current_node = current_node
                        .ok_or(Error::SetValueFailed)?
                        .borrow()
                        .next
                        .clone();
                    id += 1;
                }
                current_node.ok_or(Error::SetValueFailed)?
            }
            false => {
                let mut id = self.size - 1;
                let mut current_node = self.tail.clone();
                while id > index {
                    current_node = current_node
                        .ok_or(Error::SetValueFailed)?
                        .borrow()
                        .prev
                        .as_ref()
                        .and_then(|w| w.upgrade());
                    id -= 1;
                }
                current_node.ok_or(Error::SetValueFailed)?
            }
        };

        node.borrow_mut().set_value(value);

        Ok(())
    }

    pub fn get_value_at(&mut self, index: usize) -> Result<T>
    where
        T: Clone,
    {
        if self.size == 0 {
            return Err(Error::Empty);
        }
        if index >= self.size {
            return Err(Error::IndexOutOfBound);
        }

        let node = match index <= self.size / 2 {
            true => {
                let mut id = 0usize;
                let mut current_node = self.head.clone();
                while id < index {
                    current_node = current_node
                        .ok_or(Error::SetValueFailed)?
                        .borrow()
                        .next
                        .clone();
                    id += 1;
                }
                current_node.ok_or(Error::SetValueFailed)?
            }
            false => {
                let mut id = self.size - 1;
                let mut current_node = self.tail.clone();
                while id > index {
                    current_node = current_node
                        .ok_or(Error::SetValueFailed)?
                        .borrow()
                        .prev
                        .as_ref()
                        .and_then(|w| w.upgrade());
                    id -= 1;
                }
                current_node.ok_or(Error::SetValueFailed)?
            }
        };

        Ok(node.borrow().val.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let mut g_dll = DoubleLinkedList::<String>::new(0);

        let one = g_dll.prepend("one".to_string());
        assert_eq!(
            one.borrow().get_value_ref(),
            &g_dll.head.as_ref().unwrap().borrow().val
        );

        let two = g_dll.append("two".to_string());
        assert_eq!(
            &two.borrow().val,
            &g_dll.tail.as_ref().unwrap().borrow().val
        );

        let zero = g_dll.prepend("zero".to_string());
        assert_eq!(
            &zero.borrow().val,
            &g_dll.head.as_ref().unwrap().borrow().val
        );

        println!(">> test_add");
        println!("{}", g_dll);
    }

    #[test]
    fn test_insert() {
        let mut g_dll = DoubleLinkedList::<String>::new(0);

        let one = g_dll.append("one".to_string());
        assert_eq!(
            &one.borrow().val,
            &g_dll.head.as_ref().unwrap().borrow().val
        );

        assert_eq!(
            &one.borrow().val,
            &g_dll.tail.as_ref().unwrap().borrow().val
        );

        let two = g_dll.insert_after(one.clone(), "two".to_string()).unwrap();
        assert_eq!(
            &two.borrow().val,
            &g_dll.tail.as_ref().unwrap().borrow().val
        );

        let three = g_dll
            .insert_after(one.clone(), "three".to_string())
            .unwrap();
        assert_eq!(
            &three.borrow().val,
            &one.borrow().next.as_ref().unwrap().borrow().val
        );
        assert_eq!(
            &three.borrow().val,
            &two.borrow()
                .prev
                .as_ref()
                .unwrap()
                .upgrade()
                .unwrap()
                .borrow()
                .val
        );

        let zero = g_dll
            .insert_before(three.clone(), "zero".to_string())
            .unwrap();
        assert_eq!(
            &zero.borrow().val,
            &one.borrow().next.as_ref().unwrap().borrow().val
        );

        assert_eq!(
            &zero.borrow().val,
            &three
                .borrow()
                .prev
                .as_ref()
                .unwrap()
                .upgrade()
                .unwrap()
                .borrow()
                .val
        );

        println!(">> test_insert:");
        println!("{}", g_dll);
    }

    #[test]
    fn test_remove() {
        let mut g_dll = DoubleLinkedList::<String>::new(0);

        let one = g_dll.append("one".to_string());
        assert_eq!(
            &one.borrow().val,
            &g_dll.head.as_ref().unwrap().borrow().val
        );

        assert_eq!(
            &one.borrow().val,
            &g_dll.tail.as_ref().unwrap().borrow().val
        );

        let two = g_dll.insert_after(one.clone(), "two".to_string()).unwrap();
        assert_eq!(
            &two.borrow().val,
            &g_dll.tail.as_ref().unwrap().borrow().val
        );

        let three = g_dll
            .insert_after(one.clone(), "three".to_string())
            .unwrap();
        assert_eq!(
            &three.borrow().val,
            &one.borrow().next.as_ref().unwrap().borrow().val
        );
        assert_eq!(
            &three.borrow().val,
            &two.borrow()
                .prev
                .as_ref()
                .unwrap()
                .upgrade()
                .unwrap()
                .borrow()
                .val
        );

        let zero = g_dll
            .insert_before(three.clone(), "zero".to_string())
            .unwrap();
        assert_eq!(
            &zero.borrow().val,
            &one.borrow().next.as_ref().unwrap().borrow().val
        );

        assert_eq!(
            &zero.borrow().val,
            &three
                .borrow()
                .prev
                .as_ref()
                .unwrap()
                .upgrade()
                .unwrap()
                .borrow()
                .val
        );

        println!(">> test_remove:");
        println!("{}", &g_dll);

        {
            let five = g_dll.append("five".to_string());
            println!("five count: {}", Rc::strong_count(&five));
            let val = g_dll.remove(five.clone());
            assert_eq!(&val.unwrap(), "five");
            println!("five count: {}", Rc::strong_count(&five));
        }

        println!("three count: {}", Rc::strong_count(&three));

        let _ = g_dll.remove_at(2);
        assert_eq!(3, g_dll.size);

        println!("three count: {}", Rc::strong_count(&three));

        // remove
        println!(">> - After remove -");
        println!("{}", g_dll);
    }

    #[test]
    pub fn test_set_value() {
        println!(">> test_set_value:");

        let mut g_dll = DoubleLinkedList::new(0);
        let one = g_dll.append("one".to_string());
        assert_eq!(
            one.borrow().get_value_ref(),
            &g_dll.get_value_at(0).unwrap()
        );

        let two = g_dll.append("two".to_string());
        assert_eq!(
            two.borrow().get_value_ref(),
            &g_dll.get_value_at(1).unwrap()
        );
        println!("{}", &g_dll);

        one.borrow_mut().set_value("one-1".to_string());

        let _ = g_dll.set_value_at("two-2".to_string(), 1);
        assert_eq!("two-2".to_string(), g_dll.get_value_at(1).unwrap());

        println!("{}", &g_dll);
    }
}
