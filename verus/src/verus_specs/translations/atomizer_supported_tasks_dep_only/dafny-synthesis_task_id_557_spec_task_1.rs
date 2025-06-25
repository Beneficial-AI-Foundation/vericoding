// ATOM 
pub open spec fn IsLowerCase(c: char) -> bool
{
    97 <= c as int <= 122
}

// ATOM 
pub open spec fn IsUpperCase(c: char) -> bool
{
    65 <= c as int <= 90
}

// ATOM 
pub open spec fn IsLowerUpperPair(c: char, C: char) -> bool
{
    (c as int) == (C as int) + 32
}

// ATOM 
pub open spec fn IsUpperLowerPair(C: char, c: char) -> bool
{
    (C as int) == (c as int) - 32
}

// ATOM 
pub open spec fn ShiftMinus32(c: char) -> char
{
    ((c as int - 32) % 128) as char
}

// ATOM 
pub open spec fn Shift32(c: char) -> char
{
    ((c as int + 32) % 128) as char
}

// SPEC 
pub fn ToggleCase(s: &str) -> (v: String)
    ensures(|v| == |s|)
    ensures(forall|i: int| 0 <= i < |s| ==> if IsLowerCase(s[i]) { IsLowerUpperPair(s[i], v[i]) } else if IsUpperCase(s[i]) { IsUpperLowerPair(s[i], v[i]) } else { v[i] == s[i] })
{
}