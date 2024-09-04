```
the trait bound `ProductName: Ord` is not satisfied
the trait `Ord` is not implemented for `ProductName`rustcClick for full compiler diagnostic
slice.rs(308, 12): required by a bound in `slice::<impl [T]>::sort_by_key`
alloc::slice
impl<T> [T]
pub fn sort_by_key<K, F>(&mut self, f: F)
where
    F: FnMut(&T) -> K,
    K: Ord,
Sorts the slice with a key extraction function.

This sort is stable (i.e., does not reorder equal elements) and O(m * n * log(n)) worst-case, where the key function is O(m).
```
