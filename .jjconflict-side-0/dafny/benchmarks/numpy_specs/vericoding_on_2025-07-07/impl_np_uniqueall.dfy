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
        /* code modified by LLM (iteration 4): invariant that each element in result[0..count) came from arr[0..i) */
        invariant forall k :: 0 <= k < count ==> exists m :: 0 <= m < i && result[k] == arr[m]
        /* code modified by LLM (iteration 4): invariant ensuring uniqueness in result[0..count) */
        invariant forall k, m :: 0 <= k < count && 0 <= m < count && k != m ==> result[k] != result[m]
        /* code modified by LLM (iteration 4): fixed invariant - every element from arr[0..i) has a unique representative in result[0..count) */
        invariant forall k :: 0 <= k < i ==> (exists m :: 0 <= m < count && result[m] == arr[k])
    {
        var found := false;
        for j := 0 to count
            invariant 0 <= j <= count
            invariant found <==> exists k :: 0 <= k < j && result[k] == arr[i]
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
    {
        ret[i] := result[i];
    }
}