//SPEC
method intersect (a: array<real>, b: array<real>) returns (ret: array<real>)
    ensures ret.Length < a.Length && ret.Length < b.Length;
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> if a[i] == b[j] then exists k :: 0 <= k < ret.Length && ret[k] == a[i] else ! (exists k :: 0 <= k < ret.Length && ret[k] == a[i]);
{}