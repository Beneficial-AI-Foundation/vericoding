// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_ladder(arr: Seq<int>, l: int, r: int) -> bool {
  &&& 0 <= l <= r < arr.len()
  &&& if l == r {
    true
  } else {
    exists|k: int| l <= k <= r && 
      is_non_decreasing(arr, l, k) && 
      is_non_increasing(arr, k, r)
  }
}

spec fn is_non_decreasing(arr: Seq<int>, start: int, end: int) -> bool {
  &&& 0 <= start <= end < arr.len()
  &&& forall|i: int| start <= i < end ==> #[trigger] arr[i] <= arr[i+1]
}

spec fn is_non_increasing(arr: Seq<int>, start: int, end: int) -> bool {
  &&& 0 <= start <= end < arr.len()
  &&& forall|i: int| start <= i < end ==> #[trigger] arr[i] >= arr[i+1]
}
// </vc-preamble>

// <vc-helpers>
fn compute_nd_end(arr: Vec<i8>) -> (res: Vec<int>)
    ensures
        arr@.len() == res@.len(),
        forall|i: int| 0 <= i < arr@.len() ==> i <= res@[i] < arr@.len(),
        forall|i: int| 0 <= i < arr@.len() ==> forall|k: int| i <= k < res@[i] ==> (arr@[k] as int) <= (arr@[k+1] as int),
        forall|i: int| 0 <= i < arr@.len() ==> if res@[i] < arr@.len()-1 { (arr@[res@[i]] as int) > (arr@[res@[i]+1] as int) } else { true },
{
    let n_usize: usize = arr.len();
    let n: int = n_usize as int;
    let mut out: Vec<int> = Vec::new();

    let mut start: int = 0;
    while start < n
        invariant
            0 <= start <= n,
            out.len() == start as usize,
            forall|i: int| 0 <= i < start ==> i <= out@[i] < n,
            forall|i: int| 0 <= i < start ==> forall|k: int| i <= k < out@[i] ==> (arr@[k] as int) <= (arr@[k+1] as int),
        decreases n - start
    {
        let mut j: int = start + 1;
        while j < n && (arr[(j - 1) as usize] as int) <= (arr[j as usize] as int)
            invariant
                start < j <= n || (j == start + 1 && start + 1 <= n),
                forall|k: int| start <= k < j ==> (arr@[k] as int) <= (arr@[k+1] as int),
            decreases n - j
        {
            j = j + 1;
        }
        let seg_end: int = j - 1;
        let mut idx: int = start;
        while idx <= seg_end
            invariant
                start <= idx <= seg_end + 1,
                out.len() == idx as usize,
                forall|i: int| 0 <= i < idx ==> i <= out@[i] < n,
            decreases seg_end - idx + 1
        {
            out.push(seg_end);
            idx = idx + 1;
        }
        start = j;
    }

    out
}

fn compute_ni_start(arr: Vec<i8>) -> (res: Vec<int>)
    ensures
        arr@.len() == res@.len(),
        forall|i: int| 0 <= i < arr@.len() ==> 0 <= res@[i] <= i,
        forall|i: int| 0 <= i < arr@.len() ==> forall|k: int| res@[i] <= k < i ==> (arr@[k] as int) >= (arr@[k+1] as int),
        forall|i: int| 0 <= i < arr@.len() ==> if res@[i] > 0 { (arr@[(res@[i]-1)] as int) < (arr@[res@[i]] as int) } else { true },
{
    let n_usize: usize = arr.len();
    let n: int = n_usize as int;

    let mut out: Vec<int> = Vec::new();

    let mut start: int = 0;
    while start < n
        invariant
            0 <= start <= n,
            out.len() == start as usize,
            forall|i: int| 0 <= i < start ==> 0 <= out@[i] <= i,
            forall|i: int| 0 <= i < start ==> forall|k: int| out@[i] <= k < i ==> (arr@[k] as int) >= (arr@[k+1] as int),
        decreases n - start
    {
        let mut j: int = start + 1;
        while j < n && (arr[(j - 1) as usize] as int) >= (arr[j as usize] as int)
            invariant
                start < j <= n || (j == start + 1 && start + 1 <= n),
                forall|k: int| start <= k < j ==> (arr@[k] as int) >= (arr@[k+1] as int),
            decreases n - j
        {
            j = j + 1;
        }
        // segment [start, j-1] is non-increasing; for each idx in it, ni_start[idx] = start
        let mut idx: int = start;
        while idx < j
            invariant
                start <= idx <= j,
                out.len() == idx as usize,
                forall|i: int| 0 <= i < idx ==> 0 <= out@[i] <= i,
            decreases j - idx
        {
            out.push(start);
            idx = idx + 1;
        }
        start = j;
    }

    out
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, arr: Vec<i8>, queries: Vec<(i8, i8)>) -> (results: Vec<Vec<char>>)
  requires 
    n >= 1 && m >= 1,
    arr@.len() == n as int,
    queries@.len() == m as int,
    forall|i: int| 0 <= i < m as int ==> 1 <= #[trigger] queries@[i].0 as int <= queries@[i].1 as int <= n as int,
  ensures 
    results@.len() == m as int,
    forall|i: int| 0 <= i < m as int ==> #[trigger] results@[i]@ == seq!['Y', 'e', 's'] || results@[i]@ == seq!['N', 'o'],
    forall|i: int| 0 <= i < m as int ==> 
      (#[trigger] results@[i]@ == seq!['Y', 'e', 's'] <==> is_ladder(arr@.map(|_i, v| v as int), queries@[i].0 as int - 1, queries@[i].1 as int - 1)),
// </vc-spec>
// <vc-code>
{
    let n_usize: usize = arr.len();
    let n: int = n_usize as int;

    // compute arrays describing maximal non-decreasing stretch from each start
    let nd = compute_nd_end(arr.clone());
    // compute arrays describing minimal start of non-increasing stretch ending at each index
    let ni = compute_ni_start(arr.clone());

    let mut results: Vec<Vec<char>> = Vec::new();

    // prebuild Yes/No vectors
    let mut yes_v: Vec<char> = Vec::new();
    yes_v.push('Y'); yes_v.push('e'); yes_v.push('s');
    let mut no_v: Vec<char> = Vec::new();
    no_v.push('N'); no_v.push('o');

    let m_usize: usize = queries.len();
    let m: int = m_usize as int;

    let mut qi: int = 0;
    while qi < m
        invariant
            0 <= qi <= m,
            results.len() == qi as usize,
        decreases m - qi
    {
        let (a_i, b_i) = queries[qi as usize];
        let l: int = a_i as int - 1;
        let r: int = b_i as int - 1;
        let l_usize: usize = l as usize;
        let r_usize: usize = r as usize;

        let cond: bool = nd[l_usize] >= ni[r_usize];
        if cond {
            results.push(yes_v.clone());
        } else {
            results.push(no_v.clone());
        }

        // Proof of correctness for this query: the condition on nd/ni is equivalent to is_ladder
        proof {
            // abbreviations for seq views
            let arr_seq: Seq<int> = arr@.map(|_i, v: i8| v as int);

            // From helper ensures we have the following facts:
            // 1) For index l: for all t in l..nd[l]-1, arr[t] <= arr[t+1]
            assert(0 <= l && l <= r && r < n);
            assert(0 <= l && l < n && 0 <= r && r < n);

            // forward implication: if cond then is_ladder
            if cond {
                // choose k = ni[r]
                let k: int = ni[r_usize];
                // k is in range
                assert(l <= k && k <= r);
                // arr non-decreasing from l to k because k <= nd[l]
                assert(forall|t: int| l <= t < k ==> arr_seq[t] <= arr_seq[t+1]);
                // arr non-increasing from k to r because of ni start property
                assert(forall|t: int| k <= t < r ==> arr_seq[t] >= arr_seq[t+1]);
                // thus is_ladder
                assert(is_non_decreasing(arr_seq, l, k));
                assert(is_non_increasing(arr_seq, k, r));
                assert(is_ladder(arr_seq, l, r));
                // and the produced result is Yes
                assert(results@[qi]@ == seq!['Y','e','s']);
            } else {
                // show that not is_ladder
                // assume for contradiction there exists k with both properties
                if is_ladder(arr_seq, l, r) {
                    // extract witness k from definition of is_ladder
                    // by the spec of is_ladder there exists k with l<=k<=r and both properties
                    let k = choose(|k: int| l <= k <= r && is_non_decreasing(arr_seq, l, k) && is_non_increasing(arr_seq, k, r));
                    // from maximality of nd[l] we have nd[l] >= k
                    assert(nd[l_usize] >= k);
                    // from minimality of ni[r] we have ni[r] <= k
                    assert(ni[r_usize] <= k);
                    // combine to get nd[l] >= ni[r], contradiction with else branch
                    assert(nd[l_usize] >= ni[r_usize]);
                    // contradiction reached, so this branch is impossible
                    assert(false);
                }
                // therefore not is_ladder
                assert(!is_ladder(arr_seq, l, r));
                assert(results@[qi]@ == seq!['N','o']);
            }
        }

        qi = qi + 1;
    }

    results
}

// </vc-code>


}

fn main() {}