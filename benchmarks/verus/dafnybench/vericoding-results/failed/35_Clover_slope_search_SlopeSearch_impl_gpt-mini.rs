use vstd::prelude::*;

verus! {

// <vc-helpers>
fn slope_search_rec(a: &Vec<Vec<i32>>, key: i32, i: usize, j: usize) -> (result: (usize, usize))
  requires
      a.len() > 0,
      forall|ii: int| 0 <= ii < a.len() as int ==> #[trigger] a@[ii] .len() == a@[0].len(),
      a@[0].len() > 0,
      // Each row is sorted (non-decreasing)
      forall|ii: int, jj: int, jjp: int| 
          0 <= ii < a.len() as int && 0 <= jj < jjp < a@[0].len() as int
          ==> #[trigger] a@[ii]@[jj] <= #[trigger] a@[ii]@[jjp],
      // Each column is sorted (non-decreasing)  
      forall|ii: int, iip: int, jj: int| 
          0 <= ii < iip < a.len() as int && 0 <= jj < a@[0].len() as int
          ==> #[trigger] a@[ii]@[jj] <= #[trigger] a@[iip]@[jj],
      // Key exists somewhere in the matrix
      exists|pp: int, qq: int| 0 <= pp < a.len() as int && 0 <= qq < a@[0].len() as int && #[trigger] a@[pp]@[qq] == key,
      // current search region indices
      i < a.len(),
      j < a[0].len(),
      // additionally ensure j is valid for row i to make indexing a[i][j] safe
      j < a[i].len(),
      // Region invariant: any occurrence of key must lie in rows >= i and cols <= j
      forall|pp: int, qq: int| 0 <= pp < a.len() as int && 0 <= qq < a@[0].len() as int && a@[pp]@[qq] == key ==> pp >= i as int && qq <= j as int
  ensures
      result.0 < a.len(),
      result.1 < a[0].len(),
      a@[result.0 as int]@[result.1 as int] == key
  decreases ((a.len() - i + (j + 1)) as nat)
{
    let rows: usize = a.len();
    let cols: usize = a[0].len();

    // ensure indexing preconditions are available
    proof {
        // instantiate row length equality for row i
        assert(a@[i as int].len() == a@[0].len());
        // from requires j < a[0].len() and equality, j < a[i].len()
        assert(j < a[i].len());
    }

    // current value
    let v: i32 = a[i][j];

    if v == key {
        (i, j)
    } else if v > key {
        // We will recurse on (i, j-1). Need to show j >= 1 and the region invariant holds for j-1.
        proof {
            // use the global existence to obtain a witness
            let (pp, qq) = choose|pp: int, qq: int| 0 <= pp < a.len() as int && 0 <= qq < a@[0].len() as int && a@[pp]@[qq] == key;

            // From the region invariant, any witness satisfies pp >= i and qq <= j
            assert(pp >= i as int);
            assert(qq <= j as int);

            // If j == 0, then qq == 0. But then by column monotonicity, since pp >= i, a[pp][0] >= a[i][0] = v > key,
            // contradicting a[pp][qq] == key. Hence j >= 1.
            if j == 0 {
                // qq <= j == 0 and qq >= 0 implies qq == 0
                assert(qq == 0);
                // If pp == i then a[pp][qq] == a[i][j] and a[i][j] = v > key contradiction
                if pp == i as int {
                    assert(a@[pp]@[qq] == key);
                    assert(a@[i as int]@[j as int] == v);
                    assert(v > key);
                    assert(false);
                } else {
                    // pp > i
                    // from column monotonicity: a[i][j] <= a[pp][j]
                    assert(a@[i as int]@[j as int] <= a@[pp]@[j as int]);
                    // hence a[pp][j] > key, contradicting a[pp][qq] == key with qq == j
                    assert(a@[pp]@[j as int] > key);
                    assert(false);
                }
            }

            // Now prove new region invariant: any key occurrence must have column <= j-1.
            // Take arbitrary p,q with a[p][q] == key. From original invariant q <= j.
            // If q == j, then since p >= i, a[i][j] <= a[p][j], but a[i][j] = v > key, contradiction. So q != j, hence q <= j-1.
            assert(forall|p: int, q: int|
                0 <= p < a.len() as int && 0 <= q < a@[0].len() as int && a@[p]@[q] == key
                ==>
                p >= i as int && q <= (j as int) - 1
            );
        }

        slope_search_rec(a, key, i, j - 1)
    } else {
        // v < key: recurse on (i+1, j). Need to show i+1 < rows and region invariant for i+1.
        proof {
            let (pp, qq) = choose|pp: int, qq: int| 0 <= pp < a.len() as int && 0 <= qq < a@[0].len() as int && a@[pp]@[qq] == key;

            // From region invariant, pp >= i and qq <= j
            assert(pp >= i as int);
            assert(qq <= j as int);

            // If i == rows - 1, then pp == i (since pp < rows), and qq <= j.
            // But row monotonicity implies for any q <= j, a[i][q] <= a[i][j] < key, contradiction with a[pp][qq] == key.
            if i == rows - 1 {
                // pp >= i and pp < rows ==> pp == i
                assert(pp == i as int);
                // a[pp][qq] <= a[pp][j] = a[i][j] = v < key, so cannot be equal to key
                assert(a@[pp]@[qq] <= a@[pp]@[j as int]);
                assert(a@[pp]@[j as int] == a@[i as int]@[j as int]);
                assert(a@[i as int]@[j as int] == v);
                assert(v < key);
                assert(false);
            }

            // Now prove new region invariant: any key occurrence must have row >= i+1.
            // Take arbitrary p,q with a[p][q] == key. From original invariant p >= i.
            // If p == i, then a[i][q] <= a[i][j] = v < key, contradiction. So p >= i+1.
            assert(forall|p: int, q: int|
                0 <= p < a.len() as int && 0 <= q < a@[0].len() as int && a@[p]@[q] == key
                ==>
                p >= (i as int) + 1 && q <= j as int
            );
        }

        slope_search_rec(a, key, i + 1, j)
    }
}
// </vc-helpers>

// <vc-spec>
fn slope_search(a: &Vec<Vec<i32>>, key: i32) -> (result: (usize, usize))
  requires 
      a.len() > 0,
      forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i].len() == a@[0].len(),
      a@[0].len() > 0,
      // Each row is sorted (non-decreasing)
      forall|i: int, j: int, j_prime: int| 
          0 <= i < a.len() && 0 <= j < j_prime < a@[0].len()
          ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i]@[j_prime],
      // Each column is sorted (non-decreasing)  
      forall|i: int, i_prime: int, j: int| 
          0 <= i < i_prime < a.len() && 0 <= j < a@[0].len()
          ==> #[trigger] a@[i]@[j] <= #[trigger] a@[i_prime]@[j],
      // Key exists in the matrix
      exists|i: int, j: int| 
          0 <= i < a.len() && 0 <= j < a@[0].len()
          && #[trigger] a@[i]@[j] == key
  ensures
      result.0 < a.len(),
      result.1 < a@[0].len(),
      a@[result.0 as int]@[result.1 as int] == key
// </vc-spec>
// <vc-code>
{
    let rows: usize = a.len();
    let cols: usize = a[0].len();
    slope_search_rec(a, key, 0usize, cols - 1usize)
}
// </vc-code>

fn main() {
}

}