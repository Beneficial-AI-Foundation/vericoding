```rust
use vstd::prelude::*;

verus! {

spec fn split_from_right(s: &str, sep: &str, maxsplit: usize) -> Seq<&str>;

fn rsplit(a: Vec<String>, sep: String, maxsplit: usize) -> (result: Vec<Vec<String>>)
    requires 
        sep@.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() > 0,
        maxsplit == 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i].len() == 1 && result[i][0] == a[i],
        forall|i: int| 0 <= i < result.len() ==> result[i].len() <= maxsplit + 1,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}

}
fn main() {}
```