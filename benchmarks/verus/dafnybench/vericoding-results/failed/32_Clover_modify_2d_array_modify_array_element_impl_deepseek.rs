use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn distinct_implies_non_equal<T>(a: Seq<Seq<T>>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
        i != j,
        forall|k: int, l: int| 
            0 <= k < a.len() && 0 <= l < a.len() && k != l ==> 
            !equal(a[k], a[l]),
    ensures
        !equal(a[i], a[j]),
{
}

proof fn update_preserves_distinctness<T>(a: Seq<Seq<T>>, i: int, j: int, val: T) 
    requires
        0 <= i < a.len(),
        0 <= j < a[i].len(),
        forall|k: int, l: int| 
            0 <= k < a.len() && 0 <= l < a.len() && k != l ==> 
            !equal(a[k], a[l]),
    ensures
        forall|k: int, l: int| 
            0 <= k < a.update(i, a[i].update(j, val)).len() && 
            0 <= l < a.update(i, a[i].update(j, val)).len() && 
            k != l ==> 
            !equal(a.update(i, a[i].update(j, val))[k], a.update(i, a[i].update(j, val))[l]),
{
    assert forall|k: int, m: int| 
        0 <= k < a.update(i, a[i].update(j, val)).len() && 
        0 <= m < a.update(i, a[i].update(j, val)).len() && 
        k != m implies 
        !equal(a.update(i, a[i].update(j, val))[k], a.update(i, a[i].update(j, val))[m]) by {
        if k == i && m == i {
            // k != m, so this case is impossible
        } else if k == i {
            distinct_implies_non_equal(a, i, m);
            assert(!equal(a[i], a[m]));
            assert(a.update(i, a[i].update(j, val))[m] == a[m]);
            assert(a.update(i, a[i].update(j, val))[i] == a[i].update(j, val));
            assert(!equal(a[i].update(j, val), a[m]));
        } else if m == i {
            distinct_implies_non_equal(a, k, i);
            assert(!equal(a[k], a[i]));
            assert(a.update(i, a[i].update(j, val))[k] == a[k]);
            assert(a.update(i, a[i].update(j, val))[i] == a[i].update(j, val));
            assert(!equal(a[k], a[i].update(j, val)));
        } else {
            distinct_implies_non_equal(a, k, m);
            assert(!equal(a[k], a[m]));
            assert(a.update(i, a[i].update(j, val))[k] == a[k]);
            assert(a.update(i, a[i].update(j, val))[m] == a[m]);
            assert(!equal(a[k], a[m]));
        }
    };
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
    let old_arr = arr@;
    proof {
        let seq_old_arr = old_arr.to_Seq_of_Seqs();
        update_preserves_distinctness(seq_old_arr, index1 as int, index2 as int, val);
    }
    arr[index1][index2] = val;
    proof {
        assert(arr@ == old_arr.update(index1 as int, old_arr[index1 as int].update(index2 as int, val)));
    }
}
// </vc-code>

fn main() {}

}