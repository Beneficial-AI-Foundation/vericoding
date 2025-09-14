// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified to focus on maintaining the key invariant */
lemma ProveInvariantMaintained(v: array<int>, temp: array<int>, i: int, count: int, e: int)
    requires 0 <= i < v.Length
    requires 0 <= count <= temp.Length
    requires v[i] <= e
    requires forall k :: 0 <= k < i && v[k] <= e ==> exists j :: 0 <= j < count && temp[j] == v[k]
    requires forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
    requires temp[count] == v[i]
    ensures forall k :: 0 <= k < i + 1 && v[k] <= e ==> exists j :: 0 <= j < count + 1 && temp[j] == v[k]
{
    forall k | 0 <= k < i + 1 && v[k] <= e
    ensures exists j :: 0 <= j < count + 1 && temp[j] == v[k]
    {
        if k < i {
            assert exists j :: 0 <= j < count && temp[j] == v[k];
        } else {
            assert k == i;
            assert temp[count] == v[k];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)
    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && (exists j :: 0 <= j < v.Length && v[j] == result[k])
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> (exists j :: 0 <= j < result.Length && result[j] == v[k])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added lemma call to prove invariant maintenance */
    var temp := new int[v.Length];
    var count := 0;
    
    for i := 0 to v.Length
        invariant 0 <= count <= i
        invariant forall k :: 0 <= k < count ==> temp[k] <= e
        invariant forall k :: 0 <= k < count ==> exists j :: 0 <= j < i && v[j] == temp[k]
        invariant forall k :: 0 <= k < i && v[k] <= e ==> exists j :: 0 <= j < count && temp[j] == v[k]
        invariant forall k1, k2 :: 0 <= k1 < k2 < count ==> temp[k1] != temp[k2]
        invariant forall k :: 0 <= k < count ==> exists j :: 0 <= j < v.Length && v[j] == temp[k]
    {
        if v[i] <= e {
            temp[count] := v[i];
            ProveInvariantMaintained(v, temp, i, count, e);
            count := count + 1;
        }
    }
    
    result := new int[count];
    for i := 0 to count
        invariant forall k :: 0 <= k < i ==> result[k] == temp[k]
        invariant forall k :: 0 <= k < i ==> result[k] <= e
        invariant forall k :: 0 <= k < i ==> exists j :: 0 <= j < v.Length && v[j] == result[k]
    {
        result[i] := temp[i];
    }
}
// </vc-code>
