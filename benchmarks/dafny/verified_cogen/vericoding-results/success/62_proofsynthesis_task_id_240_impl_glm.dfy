// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added precondition to ensure array length is positive */
method cloneArrayExceptLast(arr: array<int>) returns (result: array<int>)
    requires arr.Length > 0
    ensures result.Length == arr.Length - 1
    ensures forall i :: 0 <= i < arr.Length - 1 ==> result[i] == arr[i]
{
    var len := arr.Length - 1;
    result := new int[len];
    forall i | 0 <= i < len {
        result[i] := arr[i];
    }
}
// </vc-helpers>

// <vc-spec>
method ReplaceLastElement(first: array<int>, second: array<int>) returns (replacedList: array<int>)
    requires first.Length > 0
    ensures replacedList.Length == first.Length - 1 + second.Length
    ensures forall i :: 0 <= i < first.Length - 1 ==> replacedList[i] == first[i]
    ensures forall i :: 0 <= i < second.Length ==> replacedList[first.Length - 1 + i] == second[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no changes needed, but updating iteration number */
{
    var firstWithoutLast := cloneArrayExceptLast(first);
    var len := first.Length - 1 + second.Length;
    replacedList := new int[len];
    
    forall i | 0 <= i < firstWithoutLast.Length {
        replacedList[i] := firstWithoutLast[i];
    }
    
    forall i | 0 <= i < second.Length {
        replacedList[firstWithoutLast.Length + i] := second[i];
    }
}
// </vc-code>
