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
{
  if x <= y && y <= z then (x, y, z)
  else if x <= z && z <= y then (x, z, y)
  else if y <= x && x <= z then (y, x, z)
  else if y <= z && z <= x then (y, z, x)
  else if z <= x && x <= y then (z, x, y)
  else (z, y, x)
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
  assert |nums| == 3;
  assert 0 <= 0 < |nums|;
  assert 0 <= 1 < |nums|;
  assert 0 <= 2 < |nums|;
  assert nums[0] > 0 && nums[0] <= 1500;
  assert nums[1] > 0 && nums[1] <= 1500;
  assert nums[2] > 0 && nums[2] <= 1500;

  result := computeResult(nums[0], nums[1], nums[2]);
  assert result == "YES" || result == "NO";
}
// </vc-code>

