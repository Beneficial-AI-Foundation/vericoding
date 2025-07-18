//IMPL element_wise_module

/* code modified by LLM (iteration 2): Fixed compilation errors - removed Unicode characters and cleaned up comments */
method element_wise_module(arr1: seq<int>, arr2: seq<int>) returns (result: seq<int>)
    requires arr1 != [] && arr2 != []
    requires |arr1| == |arr2|
    requires forall i :: 0 <= i < |arr2| ==> arr2[i] != 0
    ensures |result| == |arr1|
    ensures forall i :: 0 <= i < |result| ==> result[i] == arr1[i] % arr2[i]
{
    result := [];
    var i := 0;
    
    while i < |arr1|
        invariant 0 <= i <= |arr1|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == arr1[j] % arr2[j]
    {
        var mod_result := arr1[i] % arr2[i];
        result := result + [mod_result];
        i := i + 1;
    }
}