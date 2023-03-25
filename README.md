# Soot

**S**elf **O**bject **o**f **T**error - A library to create self-referential objects without unsafe blocks or boilerplate.

```rust
use soot::soot;
use std::{
    cell::RefCell,
    iter::Cloned,
    pin::pin,
    rc::Rc,
    slice,
};

fn make_thing<T: Clone>(v: &Rc<RefCell<[T]>>) -> soot![type (&'a mut [T], Cloned<slice::IterMut<'a, T>>); '_] {
    soot! {
        do {
            let mut borrowed = v.borrow_mut();
            let (left, right) = borrowed.split_at_mut(3);
        }
        => (left, right.iter().cloned())
    }
}

fn main() {
    let target = Rc::new(RefCell::new([3, 2, 1, 4, 5]));
    let (left_slice, iter) = pin!(make_thing()).get();
    
    println!("Left slice: {left_slice:?}");

    for value in iter {
        println!("{value}");
    }
}
```

## Introduction

==TODO==