

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method intersperse(numbers: seq<int>, delimeter: int) returns (res: seq<int>)
  // post-conditions-start
  ensures |numbers| != 0 ==> |numbers| * 2 - 1 == |res|
  ensures |numbers| == 0 ==> |res| == 0
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 1 ==> res[i] == delimeter
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if |numbers| == 0 {
        return [];
    } else {
        var result: seq<int> := [];
        for i := 0 to |numbers|
            invariant 0 <= i <= |numbers|
            invariant |result| == (if i == 0 then 0 else i * 2 - 1)
            invariant forall k : int :: 0 <= k < |result| && k % 2 == 0 ==> result[k] == numbers[k / 2]
            invariant forall k : int :: 0 <= k < |result| && k % 2 == 1 ==> result[k] == delimeter
        {
            if i < |numbers| {
                result := result + [numbers[i]];
                if i < |numbers| - 1 {
                    result := result + [delimeter];
                }
            }
        }
        return result;
    }
}
// </vc-code>

