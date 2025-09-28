// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helpers with correct bounds checking */
lemma MembershipPreserved(v: array<int>, temp: array<int>, result: array<int>, count: int, j: int)
    requires 0 <= j <= count <= temp.Length <= v.Length
    requires j <= result.Length
    requires forall k :: 0 <= k < count ==> temp[k] in v[..]
    requires forall k :: 0 <= k < j ==> result[k] == temp[k]
    ensures forall k :: 0 <= k < j ==> result[k] in v[..]
{
    forall k | 0 <= k < j
        ensures result[k] in v[..]
    {
        assert result[k] == temp[k];
        assert temp[k] in v[..];
    }
}

lemma InclusionLemma(v: array<int>, temp: array<int>, count: int, i: int, e: int)
    requires 0 <= i < v.Length
    requires 0 <= count < temp.Length
    requires v[i] <= e
    requires temp[count] == v[i]
    requires forall k :: 0 <= k < i && v[k] <= e ==> v[k] in temp[..count]
    ensures forall k :: 0 <= k <= i && v[k] <= e ==> v[k] in temp[..count+1]
{
    forall k | 0 <= k <= i && v[k] <= e
        ensures v[k] in temp[..count+1]
    {
        if k < i {
            assert v[k] in temp[..count];
        } else {
            assert k == i;
            assert v[k] == temp[count];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)

    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]

    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && result[k] in v[..]
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> v[k] in result[..]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds and postcondition proof */
    var temp := new int[v.Length];
    var count := 0;
    
    for i := 0 to v.Length
        invariant 0 <= count <= i
        invariant count <= temp.Length
        invariant forall k :: 0 <= k < count ==> temp[k] <= e
        invariant forall k :: 0 <= k < count ==> temp[k] in v[..]
        invariant forall k :: 0 <= k < i && v[k] <= e ==> v[k] in temp[..count]
        invariant forall k :: 0 <= k < count ==> exists m :: 0 <= m < i && v[m] == temp[k] && v[m] <= e
    {
        if v[i] <= e {
            temp[count] := v[i];
            InclusionLemma(v, temp, count, i, e);
            count := count + 1;
        }
    }
    
    result := new int[count];
    for j := 0 to count
        invariant forall k :: 0 <= k < j ==> result[k] <= e
        invariant forall k :: 0 <= k < j ==> result[k] in v[..]
        invariant forall k :: 0 <= k < j ==> result[k] == temp[k]
    {
        result[j] := temp[j];
        MembershipPreserved(v, temp, result, count, j+1);
    }
}
// </vc-code>
