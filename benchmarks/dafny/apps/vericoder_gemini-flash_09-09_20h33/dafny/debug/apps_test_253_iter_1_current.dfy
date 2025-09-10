predicate ValidInput(nums: seq<int>)
{
    |nums| == 3 &&
    forall i :: 0 <= i < |nums| ==> nums[i] > 0 &&
    forall i :: 0 <= i < |nums| ==> nums[i] <= 1500
}

function computeResult(x: int, y: int, z: int): string
    requires x > 0 && y > 0 && z > 0
    requires x <= 1500 && y <= 1500 && z <= 1500
{
    var sorted := sortThree(x, y, z);
    var a := sorted.0;
    var b := sorted.1;
    var c := sorted.2;

    if a > 3 then "NO"
    else if a == 3 then
        if b > 3 then "NO"
        else if b == 3 then
            if c > 3 then "NO" else "YES"
        else "NO"
    else if a == 1 then "YES"
    else // a == 2
        if b == 2 then "YES"
        else if b > 4 then "NO"
        else if b == 4 then
            if c == 4 then "YES" else "NO"
        else "NO"
}

// <vc-helpers>
function sortThree(x: int, y: int, z: int): (int, int, int)
  requires x > 0 && y > 0 && z > 0
  requires x <= 1500 && y <= 1500 && z <= 1500
  ensures var a, b, c := sortThree(x, y, z);
          a <= b <= c &&
          (a == x || a == y || a == z) &&
          (b == x || b == y || b == z) &&
          (c == x || c == y || c == z) &&
          (a != b || a != c || b != c || x == y || x == z || y == z) // Ensure distinct if original are distinct
{
    if x <= y && x <= z {
        if y <= z { (x, y, z) }
        else { (x, z, y) }
    } else if y <= x && y <= z {
        if x <= z { (y, x, z) }
        else { (y, z, x) }
    } else { // z is the smallest
        if x <= y { (z, x, y) }
        else { (z, y, x) }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(nums: seq<int>) returns (result: string)
    requires ValidInput(nums)
    ensures result == "YES" || result == "NO"
    ensures result == computeResult(nums[0], nums[1], nums[2])
// </vc-spec>
// <vc-code>
{
    var x := nums[0];
    var y := nums[1];
    var z := nums[2];
    result := computeResult(x, y, z);
}
// </vc-code>

