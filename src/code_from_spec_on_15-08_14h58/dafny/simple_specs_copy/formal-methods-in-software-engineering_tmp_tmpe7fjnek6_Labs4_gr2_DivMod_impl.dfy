//IMPL 
method DivMod(a: int, b: int) returns (q: int, r: int)
{
    if b > 0 {
        q := a / b;
        r := a % b;
    } else if b < 0 {
        q := a / b;
        r := a % b;
    } else {
        // b == 0, undefined behavior - we'll set default values
        q := 0;
        r := a;
    }
}

/*
  triple Hoare (| P |) S (| Q |) 
*/