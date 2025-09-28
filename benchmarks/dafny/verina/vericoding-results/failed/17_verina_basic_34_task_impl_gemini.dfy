// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
ghost function FilterEvens(s: seq<int>): seq<int>
{
    if s == [] then []
    else
        var rest := FilterEvens(s[1..]);
        if IsEven(s[0]) then [s[0]] + rest else rest
}

/* helper modified by LLM (iteration 5): added inductive proof body */
lemma {:induction s1} ConcatFilter(s1: seq<int>, s2: seq<int>)
    ensures FilterEvens(s1 + s2) == FilterEvens(s1) + FilterEvens(s2)
{
    if s1 != [] {
        ConcatFilter(s1[1..], s2);
    }
}

/* helper modified by LLM (iteration 5): added ConcatFilter call to aid proof */
lemma {:induction s} FilterEvensProps(s: seq<int>)
    ensures (forall x :: x in FilterEvens(s) ==> IsEven(x) && x in s)
    ensures (forall x :: x in s && IsEven(x) ==> x in FilterEvens(s))
    ensures forall i, j :: 0 <= i <= j < |s| && IsEven(s[i]) && IsEven(s[j]) ==>
        (exists ri, rj :: 0 <= ri < |FilterEvens(s)| && 0 <= rj < |FilterEvens(s)| && ri <= rj &&
                         FilterEvens(s)[ri] == s[i] && FilterEvens(s)[rj] == s[j])
{
    if s != [] {
        FilterEvensProps(s[1..]);
        ConcatFilter([s[0]], s[1..]); 
    }
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (result: array<int>)
    ensures forall x :: x in result[..] ==> IsEven(x) && x in arr[..]
    ensures forall x :: x in arr[..] && IsEven(x) ==> x in result[..]
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i <= j 
        && IsEven(arr[i]) && IsEven(arr[j]) ==> 
        exists ri, rj :: 0 <= ri < result.Length && 0 <= rj < result.Length 
            && ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): re-submitted code, assuming lemma fixes are sufficient */
{
    var count: nat := 0;
    var i_count: nat := 0;
    while i_count < arr.Length
        invariant 0 <= i_count <= arr.Length
        invariant count == |FilterEvens(arr[..i_count])|
    {
        if i_count < arr.Length {
            ConcatFilter(arr[..i_count], [arr[i_count]]);
        }
        if IsEven(arr[i_count]) {
            count := count + 1;
        }
        i_count := i_count + 1;
    }

    result := new int[count];
    FilterEvensProps(arr[..]);
    ConcatFilter([], arr[..]);

    var i: nat := 0;
    var r_idx: nat := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant 0 <= r_idx <= count
        invariant r_idx == |FilterEvens(arr[..i])|
        invariant result[..r_idx] == FilterEvens(arr[..i])
        invariant count == |FilterEvens(arr[..])|
    {
        ConcatFilter(arr[..i], [arr[i]]);
        if IsEven(arr[i]) {
            ConcatFilter(arr[..i], arr[i..]);
            result[r_idx] := arr[i];
            r_idx := r_idx + 1;
        }
        i := i + 1;
    }
    
    assert result[..] == FilterEvens(arr[..]);
}
// </vc-code>
