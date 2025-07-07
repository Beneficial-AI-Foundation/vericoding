//IMPL
method unique_all (arr: array<int>) returns (ret: array<int>)
    ensures ret.Length <= arr.Length
    ensures forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < ret.Length && ret[j] == arr[i]
    ensures forall i, j :: 0 <= i < ret.Length && 0 <= j < i ==> ret[i] != ret[j]
{
    var result := new int[arr.Length];
    var count := 0;
    
    for i := 0 to arr.Length
        invariant 0 <= count <= i <= arr.Length
        invariant forall k :: 0 <= k < i ==> exists j :: 0 <= j < count && result[j] == arr[k]
        invariant forall p, q :: 0 <= p < count && 0 <= q < count && p != q ==> result[p] != result[q]
        invariant forall j :: 0 <= j < count ==> exists k :: 0 <= k < i && result[j] == arr[k]
    {
        var found := false;
        for j := 0 to count
            invariant found ==> exists k :: 0 <= k < j && result[k] == arr[i]
            invariant !found ==> forall k :: 0 <= k < j ==> result[k] != arr[i]
        {
            if result[j] == arr[i] {
                found := true;
                break;
            }
        }
        
        if !found {
            result[count] := arr[i];
            count := count + 1;
        }
    }
    
    ret := new int[count];
    for i := 0 to count
        invariant 0 <= i <= count
        invariant forall k :: 0 <= k < i ==> ret[k] == result[k]
        /* code modified by LLM (iteration 4): simplified invariants to focus on essential properties */
        invariant forall p, q :: 0 <= p < i && 0 <= q < i && p != q ==> ret[p] != ret[q]
        /* code modified by LLM (iteration 4): key invariant ensuring all arr elements are covered by result */
        invariant forall k :: 0 <= k < arr.Length ==> exists j :: 0 <= j < count && result[j] == arr[k]
        invariant forall p, q :: 0 <= p < count && 0 <= q < count && p != q ==> result[p] != result[q]
    {
        ret[i] := result[i];
    }
}