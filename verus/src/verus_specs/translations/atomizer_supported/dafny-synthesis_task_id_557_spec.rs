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
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if IsLowerCase(s[i as usize]) then 
                IsLowerUpperPair(s[i as usize], v[i as usize]) 
            else if IsUpperCase(s[i as usize]) then 
                IsUpperLowerPair(s[i as usize], v[i as usize]) 
            else 
                v[i as usize] == s[i as usize]
{
}