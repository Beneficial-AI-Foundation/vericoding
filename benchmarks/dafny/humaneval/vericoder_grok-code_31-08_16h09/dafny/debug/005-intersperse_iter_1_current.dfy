

// <vc-helpers>
// No additional helpers needed
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
if (|numbers| == 0) {
    res := [];
} else {
    var result := [numbers[0]];
    for i := 1 to |numbers| - 1 {
        result := result + [delimiter, numbers[i]];
    }
    res := result;
}
// </vc-code>

