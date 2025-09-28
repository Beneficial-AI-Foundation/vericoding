use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn equal_update<T>(s1: Seq<T>, s2: Seq<T>, i: int, v: T)
    requires
        s1 =~= s2,
        0 <= i < s1.len(),
    ensures
        s1.update(i, v) =~= s2.update(i, v),
{
    assert(forall|k: int|
        0 <= k < s1.len() ==> s1.update(i, v)[k] == s2.update(i, v)[k]);
}

proof fn equal_index<T>(s1: Seq<T>, s2: Seq<T>, i: int)
    requires
        s1 =~= s2,
        0 <= i < s1.len(),
    ensures
        s1[i] == s2[i],
{
    assert(s1 =~= s2 && 0 <= i < s1.len() ==> s1[i] == s2[i]);
}

proof fn equal_len<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1 =~= s2,
    ensures
        s1.len() == s2.len(),
{
    assert(s1 =~= s2 ==> s1.len() == s2.len());
}

proof fn equal_from_seq<T>(v1: &Vec<T>, v2: &Vec<T>)
    requires
        v1@ =~= v2@,
    ensures
        equal(*v1, *v2),
{
    assert(v1@ =~= v2@);
    assert(forall|i: int| 0 <= i < v1@.len() ==> v1@[i] == v2@[i]);
    assert(forall|i: int| 0 <= i < v1@.len() ==> true);
    assert(equal(*v1, *v2));
}

fn equal_index2(s1: Vec<nat>, s2: Vec<nat>, i: usize) -> (b: bool)
    requires
        s1@ =~= s2@,
        i < s1@.len(),
    ensures
        b ==> s1[i] == s2[i],
{
    reveal(equal);
    s1@ =~= s2@ && i < s1@.len() ==> s1@[i as int] == s2@[i as int]
}
// </vc-helpers>

// <vc-spec>
fn modify_array_element(arr: &mut Vec<Vec<nat>>, index1: usize, index2: usize, val: nat)
  requires
      index1 < old(arr).len(),
      index2 < old(arr)[index1 as int].len(),
      forall|i: int, j: int| 
          0 <= i < old(arr).len() && 0 <= j < old(arr).len() && i != j ==> 
          !equal(old(arr)[i], old(arr)[j]),
  ensures
      arr.len() == old(arr).len(),
      forall|i: int| 0 <= i < arr.len() ==> equal(arr[i], old(arr)[i]),
      forall|i: int, j: int| 
          0 <= i < arr.len() && 0 <= j < arr[i].len() && 
          (i != index1 || j != index2) ==> 
          arr[i][j] == old(arr)[i][j],
      arr[index1 as int][index2 as int] == val,
// </vc-spec>
// <vc-code>
{
    let old_arr = old(arr);
    let old_val = old_arr[index1 as int][index2 as int];
    let old_inner = old_arr[index1 as int];
    let old_inner_seq = old_inner@;
    let new_inner_seq = old_inner_seq.update(index2 as int, val);
    let new_inner = Vec::from_seq(new_inner_seq);
    let new_arr_seq = old_arr@.update(index1 as int, new_inner);
    *arr = Vec::from_seq(new_arr_seq);
    
    assert(arr@.len() == old_arr@.len());
    
    proof {
        assert(forall|i: int|
            0 <= i < arr@.len() && i != index1 as int ==>
            arr@[i] =~= old_arr@[i]);
        equal_from_seq(&new_inner, &old_inner);
        assert(arr@[index1 as int] =~= old_arr@[index1 as int]);
        assert(forall|i: int| 
            0 <= i < arr@.len() ==> 
            if i == index1 as int {
                arr@[i] =~= old_arr@[i]
            } else {
                arr@[i] =~= old_arr@[i]
            });
        assert(forall|i: int| 0 <= i < arr@.len() ==> arr@[i] =~= old_arr@[i]);
        
        assert(forall|i: int| 
            0 <= i < arr@.len() ==> 
            equal(arr[i], old_arr[i]));
    }
    
    assert(forall|i: int, j: int|
        0 <= i < arr@.len() && 0 <= j < arr@[i].len() && (i != index1 as int || j != index2 as int) ==>
        arr@[i][j] == old_arr@[i][j]);
    assert(arr@[index1 as int][index2 as int] == val);
}
// </vc-code>

fn main() {}

}