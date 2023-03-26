use std::{cell::RefCell, iter::Copied, pin::pin, rc::Rc, slice};

use soot::self_ref;

fn returns_a_slice() -> self_ref![for<'a> (&'a u32, &'a [u32])] {
    self_ref!(use target in {
        let slice = [3, 2, 1, 0];
        let target = slice.split_last().unwrap();
    })
}

fn locks_a_guard<T: Copy>(
    a: &Rc<RefCell<Vec<T>>>,
) -> self_ref![for<'a> (&'a T, Copied<slice::Iter<'a, T>>); '_] {
    self_ref!(use target in {
        let a = a.borrow();
        let (last, earlier) = a.split_first().unwrap();
        let target = (last, earlier.iter().copied());
    })
}

fn main() {
    let result = pin!(returns_a_slice());
    let (value, my_slice) = result.get();
    assert_eq!(*value, 0);
    assert_eq!(my_slice, &[3, 2, 1]);

    let my_cell = Rc::new(RefCell::new(my_slice.to_vec()));
    {
        let result = pin!(locks_a_guard(&my_cell));
        let (first, mut remaining_iter) = result.get();

        assert_eq!(*first, 3);
        assert_eq!(remaining_iter.next(), Some(2));
        assert_eq!(remaining_iter.next(), Some(1));
        assert_eq!(remaining_iter.next(), None);
    }
    let exclusive = my_cell.borrow_mut();
    assert_eq!(exclusive.as_slice(), &[3, 2, 1]);
}
