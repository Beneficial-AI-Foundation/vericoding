function has_count(v: int, a: array<int>, n: int): int
    reads a  // This allows the function to read from array 'a'
    requires n >= 0 && n <= a.Length
{
    if n == 0 then 0 else
    (if a[n-1] == v then has_count(v, a, n-1) + 1 else has_count(v, a, n-1))
}

// <vc-helpers>
lemma has_count_incremental(v: int, a: array<int>, i: int)
    requires 0 <= i < a.Length
    ensures has_count(v, a, i+1) == has_count(v, a, i) + (if a[i] == v then 1 else 0)
{
    // This follows directly from the definition of has_count
}
// </vc-helpers>

// <vc-spec>
method count (v: int, a: array<int>, n: int) returns (r: int)
    requires n >= 0 && n <= a.Length;
    ensures has_count(v, a, n) == r;
// </vc-spec>
// <vc-code>
{
    r := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant r == has_count(v, a, i)
    {
        has_count_incremental(v, a, i);
        if a[i] == v {
            r := r + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

