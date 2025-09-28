// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn distinct_strings(strings: Seq<String>) -> Set<String> {
    Set::new(|s: String| exists|i: int| 0 <= i < strings.len() && strings[i] == s)
}

spec fn valid_input(strings: Seq<String>) -> bool {
    strings.len() >= 1
}
// </vc-preamble>

// <vc-helpers>
fn contains(seen: &Vec<String>, s: &String) -> (b: bool)
    ensures
        b ==> exists|i: int| 0 <= i < seen@.len() && seen@[i] == *s,
        !b ==> forall|i: int| 0 <= i < seen@.len() ==> seen@[i] != *s,
{
    let mut j: usize = 0;
    let mut found: bool = false;
    while j < seen.len()
        invariant
            j <= seen.len(),
            !found ==> forall|k: int| 0 <= k < j as int ==> seen@[k] != *s,
            found ==> exists|k: int| 0 <= k < j as int && seen@[k] == *s,
        decreases seen.len() as int - j as int
    {
        if seen[j] == *s {
            found = true;
            break;
        }
        j = j + 1;
    }
    found
}
// </vc-helpers>

// <vc-spec>
fn solve(strings: Vec<String>) -> (count: i8)
    requires 
        valid_input(strings@)
    ensures 
        count as int >= 1,
        count as int <= strings@.len(),
        count as int == distinct_strings(strings@).len()
// </vc-spec>
// <vc-code>
{
    let n: usize = strings.len();
    let mut seen: Vec<String> = Vec::new();
    let mut i: usize = 0;
    let mut count: i8 = 0;
    while i < n
        invariant
            i <= n,
            0 <= count as int,
            count as int <= i as int,
        decreases n as int - i as int
    {
        let ref_s: &String = &strings[i];
        let present = contains(&seen, ref_s);
        if !present {
            seen.push(ref_s.clone());
            if count < 127i8 {
                count = count + 1;
            }
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}