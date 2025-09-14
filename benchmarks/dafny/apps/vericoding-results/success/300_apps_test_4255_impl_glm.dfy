predicate ValidInput(ab: int, bc: int, ca: int)
{
    1 <= ab <= 100 && 1 <= bc <= 100 && 1 <= ca <= 100
}

function TriangleArea(ab: int, bc: int): int
    requires ab >= 1 && bc >= 1
{
    (ab * bc) / 2
}

predicate ValidArea(ab: int, bc: int, area: int)
    requires ab >= 1 && bc >= 1
{
    area == TriangleArea(ab, bc) && area >= 0 && area <= 5000
}

// <vc-helpers>
function DigitToChar(d: int): char
   requires 0 <= d <= 9
{
   match d
     case 0 => '0'
     case 1 => '1'
     case 2 => '2'
     case 3 => '3'
     case 4 => '4'
     case 5 => '5'
     case 6 => '6'
     case 7 => '7'
     case 8 => '8'
     case 9 => '9'
}

function IntToString(x: int): string
   requires 0 <= x <= 5000
{
   if x < 10 then
       [DigitToChar(x)]
   else
       IntToString(x / 10) + [DigitToChar(x % 10)]
}
// </vc-helpers>

// <vc-spec>
method solve(ab: int, bc: int, ca: int) returns (result: string)
    requires ValidInput(ab, bc, ca)
    ensures exists area :: ValidArea(ab, bc, area) && result == IntToString(area) + "\n"
// </vc-spec>
// <vc-code>
{
    var area := TriangleArea(ab, bc);
    result := IntToString(area) + "\n";
}
// </vc-code>

