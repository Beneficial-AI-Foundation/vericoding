use vstd::prelude::*;

verus! {

spec fn how_many_times(string: Seq<char>, substring: Seq<char>) -> (result:nat)
    decreases string.len(),
{
    if (string.len() == 0) {
        0
    } else if substring.is_prefix_of(string) {
        1 + how_many_times(string.skip(1), substring)
    } else {
        how_many_times(string.skip(1), substring)
    }
}
// pure-end
// pure-end

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// pure-end

// <vc-helpers>
#[verifier(external_body)]
#[cfg(target_arch = "x86_64")]
unsafe fn usize_to_u32(n: usize) -> (i: u32)
{
    n as u32
}

#[verifier(external_body)]
#[cfg(target_arch = "aarch64")]
unsafe fn usize_to_u32(n: usize) -> (i: u32)
{
    n as u32
}

#[verifier(inline)]
fn checked_add_u32(a: u32, b: u32) -> (res: (result: u32, overflow: bool))
    ensures
        res.overflow == ((a as u64 + b as u64) > u32::MAX as u64),
        !res.overflow ==> res.result == a + b,
        res.overflow  ==> (res.result == (a as u64 + b as u64) as u32), // Any value is fine on overflow, but this makes it explicit.
{
    let (result, overflow) = a.overflowing_add(b);
    (result, overflow)
}
// </vc-helpers>

// <vc-spec>
fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)
    // pre-conditions-start
    requires
        substring.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut count: u32 = 0;
    let mut i: usize = 0;
    let mut overflow: bool = false;

    // We can prove this by induction on `string.len() - i`.
    // The base case is when `i == string.len()`.
    // The inductive step is when `i < string.len()`.
    // This allows us to connect the loop invariant to the postcondition.
    // The `ensures` clause uses `how_many_times(string, substring)` on the original string,
    // so we need to track the count from the beginning of the string.
    // The loop calculates `how_many_times(string.subsequence(i), substring)` and accumulates it to `count`.
    // If the count overflows, `overflow` becomes true and we can directly return `None`.

    #[invariant]
    // Loop invariant 1: if `overflow` is false, `count` holds the result of `how_many_times(string.subsequence(0, i), substring)` and that's equal to `how_many_times(string@.subsequence(0, i), substring@)`.
    // Loop invariant 2: if `overflow` is true, `how_many_times(string@.subsequence(0, i), substring@)` > u32::MAX.
    // Loop invariant 3: `i` is a valid index for `string`.
    // Loop invariant 4: `substring.len()` is at least 1.
    while i <= string.len()
        invariant
            i <= string.len(),
            substring.len() >= 1,
            // The accumulation property requires the subsequence to be from the beginning of the string.
            // When overflow is false, count holds the correct value up to index i.
            // When overflow is true, it means the count from the beginning up to index i has exceeded u32::MAX.
            inner_expr_how_many_times_impl(if overflow { None } else { Some(count) }, string.subsequence(0, i), substring),
        decreases string.len() - i
    {
        if overflow { // If overflow already occurred, no need to continue adding.
            i += 1;
            continue;
        }

        if i + substring.len() <= string.len() {
            let mut matches = true;
            let mut j: usize = 0;
            while j < substring.len()
                invariant
                    j <= substring.len(),
                    matches == (string.subsequence(i as int, (i + j) as int)@ == substring.subsequence(0, j)@),
                    i + j <= string.len(),
                    substring.len() >= 1, // Add this invariant since it's a precondition
                decreases substring.len() - j
            {
                if string[i + j] != substring[j] {
                    matches = false;
                }
                j += 1;
            }

            if matches {
                assert(substring.len() <= string.len()); // This ensures the `i + substring.len()` check works as expected
                let (new_count, ov) = checked_add_u32(count, 1);
                count = new_count;
                overflow = ov;
            }
        }
        i += 1;
    }

    // After the loop, `i == string.len()`.
    // So the loop invariant implies `inner_expr_how_many_times_impl(if overflow { None } else { Some(count) }, string, substring)`.
    if overflow {
        None
    } else {
        Some(count)
    }
}
// </vc-code>

} // verus!
fn main() {}