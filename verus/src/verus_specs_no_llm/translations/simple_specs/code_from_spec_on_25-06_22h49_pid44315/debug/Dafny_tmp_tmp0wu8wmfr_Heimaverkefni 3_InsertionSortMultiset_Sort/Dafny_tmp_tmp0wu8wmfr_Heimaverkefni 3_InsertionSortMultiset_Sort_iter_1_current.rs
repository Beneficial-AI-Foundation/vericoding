use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Search(s: Seq<int>, x: int) -> (k: int)
    requires forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
    ensures 0 <= k <= s.len()
    ensures forall|i: int| 0 <= i < k ==> s[i] <= x
    ensures forall|i: int| k <= i < s.len() ==> s[i] >= x
    ensures forall|z: int| z in s.subrange(0, k) ==> z <= x
    ensures forall|z: int| z in s.subrange(k, s.len() as int) ==> z >= x
    ensures s == s.subrange(0, k) + s.subrange(k, s.len() as int)
{
    let mut k = 0;
    
    while k < s.len()
        invariant 0 <= k <= s.len()
        invariant forall|i: int| 0 <= i < k ==> s[i] <= x
        invariant forall|i: int| k <= i < s.len() ==> s[i] >= x || i == k
    {
        if s[k] >= x {
            break;
        }
        k = k + 1;
    }
    
    k
}

fn Sort(m: Seq<int>) -> (r: Seq<int>)
    ensures r.len() == m.len()
    ensures forall|p: int, q: int| 0 <= p < q < r.len() ==> r[p] <= r[q]
    ensures multiset![r] == multiset![m]
{
    if m.len() == 0 {
        return seq![];
    }
    
    // Simple insertion sort implementation
    let mut result = seq![m[0]];
    let mut i = 1;
    
    while i < m.len()
        invariant 1 <= i <= m.len()
        invariant result.len() == i
        invariant forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q]
        invariant multiset![result] + multiset![m.subrange(i, m.len() as int)] == multiset![m]
    {
        let value = m[i];
        let mut j = 0;
        
        // Find insertion position
        while j < result.len() && result[j] <= value
            invariant 0 <= j <= result.len()
        {
            j = j + 1;
        }
        
        // Insert value at position j
        result = result.subrange(0, j) + seq![value] + result.subrange(j, result.len() as int);
        i = i + 1;
    }
    
    result
}

}