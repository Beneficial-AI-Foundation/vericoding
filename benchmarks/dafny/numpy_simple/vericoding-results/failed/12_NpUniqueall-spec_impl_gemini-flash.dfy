// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed argument type for IsUnique to accept array<int> instead of seq<int> */
predicate IsUnique(a: array<int>)
{
    forall i, j :: 0 <= i < a.Length && 0 <= j < i ==> a[i] != a[j]
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
/* code modified by LLM (iteration 5): fixed `tempRet[0..count]` type issue by calling unique predicate with array */
{
    var tempRet := new int[arr.Length];
    var count := 0;

    if arr.Length > 0 {
        for i := 0 to arr.Length - 1
            invariant 0 <= i <= arr.Length
            invariant 0 <= count <= i + 1
            invariant count <= tempRet.Length
            invariant IsUnique(tempRet)
            invariant forall k :: 0 <= k < count ==> exists l :: 0 <= l < i && arr[l] == tempRet[k]
            invariant forall l :: 0 <= l < i ==> (exists k :: 0 <= k < count && tempRet[k] == arr[l])
        {
            var isPresent := false;
            for j := 0 to count - 1
                invariant 0 <= j <= count
                invariant isPresent == (exists k_j :: 0 <= k_j < j && tempRet[k_j] == arr[i])
            {
                if tempRet[j] == arr[i] {
                    isPresent := true;
                    break;
                }
            }
            if !isPresent {
                tempRet[count] := arr[i];
                count := count + 1;
            }
        }
    }
    
    ret := new int[count];
    if count > 0 {
        for k := 0 to count - 1
            invariant 0 <= k <= count
            invariant forall x :: 0 <= x < k ==> ret[x] == tempRet[x]
        {
            ret[k] := tempRet[k];
        }
    }
}
// </vc-code>
