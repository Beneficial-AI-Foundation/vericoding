// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fix function implementation by adding a return type and renaming the function to avoid conflict. Also removed the extra 'then' keyword. */
function findSmallestMissing(s: array<int>, start: int, end: int): int
{
    if start > end then start
    else if start == end then start
    else {
        var mid := (start + end) / 2;
        if s[mid] == mid then findSmallestMissing(s, mid + 1, end)
        else findSmallestMissing(s, start, mid)
    }
}
// </vc-helpers>

// <vc-spec>
method SmallestMissingNumber(s: array<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < s.Length ==> s[i] <= s[j]
    requires forall i :: 0 <= i < s.Length ==> s[i] >= 0
    requires s.Length <= 100_000
    ensures 0 <= v
    ensures forall i :: 0 <= i < s.Length ==> s[i] != v
    ensures forall k {:trigger} :: 0 <= k < v ==> exists j :: 0 <= j < s.Length && s[j] == k
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix compilation error related to `lbrace expected` and invalid keyword `тогда`. */
{
    if s.Length == 0 then return 0;
    if s[0] != 0 then return 0;
    v := findSmallestMissing(s, 0, s.Length - 1);
    if v == s.Length && s[s.Length - 1] == s.Length - 1 then return s.Length
    else if v == s.Length then return s.Length
    else return v;
}
// </vc-code>
