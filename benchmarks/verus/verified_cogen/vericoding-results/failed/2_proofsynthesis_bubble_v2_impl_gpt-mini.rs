// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> (result:bool) {
    forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
}

spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> (result:bool) {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): initialize r to identity permutation */
proof fn init_identity_r(r: &mut Vec<usize>, n: usize)
    ensures
        r.len() == n,
        forall |i: int| 0 <= i < (n as int) ==> r@[i] == (i as usize),
{
    r.clear();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i,
        decreases
            n - i
    {
        r.push(i);
        i += 1;
    }
}

// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)

    ensures
        sorted_between(nums@, 0, nums@.len() as int),
        exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): capture old sequence in a proof block and implement selection sort with parallel index vector */
{
    proof {
        let _s_old: Seq<u32> = nums@;
    }

    let n: usize = nums.len();
    let mut r: Vec<usize> = Vec::new();

    let mut k: usize = 0;
    while k < n
        invariant
            r.len() == k,
        decreases
            n - k
    {
        r.push(k);
        k += 1;
    }

    proof {
        init_identity_r(&mut r, n);
    }

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            sorted_between(nums@, 0, i as int),
        decreases
            n - i
    {
        let mut m: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant
                i <= m,
                m < n,
                i + 1 <= j,
                j <= n,
                forall |t: int| (i as int) <= t < (j as int) ==> nums@[(m as int)] <= nums@[t],
            decreases
                n - j
        {
            if nums[j] < nums[m] {
                m = j;
            }
            j += 1;
        }

        if i != m {
            if i < m {
                let vi: u32 = nums.remove(i);
                let vm: u32 = nums.remove(m - 1);
                nums.insert(i, vm);
                nums.insert(m, vi);

                let ri: usize = r.remove(i);
                let rm: usize = r.remove(m - 1);
                r.insert(i, rm);
                r.insert(m, ri);
            } else {
                let vi: u32 = nums.remove(m);
                let vm: u32 = nums.remove(i - 1);
                nums.insert(m, vm);
                nums.insert(i, vi);

                let ri: usize = r.remove(m);
                let rm: usize = r.remove(i - 1);
                r.insert(m, rm);
                r.insert(i, ri);
            }
        }

        i += 1;
    }

    proof {
        assert(sorted_between(nums@, 0, n as int));
        assert(is_reorder_of(r@.map_values(|x: usize| (x as int)), nums@, old(nums)@));
        assert(exists |rr: Seq<int>| is_reorder_of(rr, nums@, old(nums)@));
    }
}

// </vc-code>

}
fn main() {}