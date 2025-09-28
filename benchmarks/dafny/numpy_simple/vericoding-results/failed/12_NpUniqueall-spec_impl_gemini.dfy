// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no functional change */
method Find(a: array<int>, n: int, x: int) returns (found: bool)
    requires 0 <= n <= a.Length
    ensures found <==> (exists i :: 0 <= i < n && a[i] == x)
{
    found := false;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant found <==> (exists k :: 0 <= k < i && a[k] == x)
    {
        if a[i] == x {
            found := true;
            return;
        }
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method UniqueAll(arr: array<int>) returns (ret: array<int>)
    ensures
        ret.Length <= arr.Length &&
        (forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < ret.Length && ret[j] == arr[i]) &&
        (forall i, j :: 0 <= i < ret.Length && 0 <= j < i ==> ret[i] != ret[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): rephrased set-based invariants to be value-based */
    var temp_ret := new int[arr.Length];
    var count := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant 0 <= count <= i
        invariant forall k, l :: 0 <= k < count && 0 <= l < k ==> temp_ret[k] != temp_ret[l]
        invariant forall val :: (exists k :: 0 <= k < i && arr[k] == val) ==> (exists j :: 0 <= j < count && temp_ret[j] == val)
        invariant forall val :: (exists j :: 0 <= j < count && temp_ret[j] == val) ==> (exists k :: 0 <= k < i && arr[k] == val)
    {
        var x := arr[i];
        var found := Find(temp_ret, count, x);
        if !found {
            temp_ret[count] := x;
            count := count + 1;
        }
        assert exists j :: 0 <= j < count && temp_ret[j] == arr[i];
        i := i + 1;
    }

    ret := new int[count];
    var j := 0;
    while j < count
        invariant 0 <= j <= count
        invariant ret.Length == count
        invariant forall k :: 0 <= k < j ==> ret[k] == temp_ret[k]
        invariant forall k, l :: 0 <= k < count && 0 <= l < k ==> temp_ret[k] != temp_ret[l]
        invariant forall val :: (exists k :: 0 <= k < arr.Length && arr[k] == val) ==> (exists l :: 0 <= l < count && temp_ret[l] == val)
    {
        ret[j] := temp_ret[j];
        j := j + 1;
    }
}
// </vc-code>
