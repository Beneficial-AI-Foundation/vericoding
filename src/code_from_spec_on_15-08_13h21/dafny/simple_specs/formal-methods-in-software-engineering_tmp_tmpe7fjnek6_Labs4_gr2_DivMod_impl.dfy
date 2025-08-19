//IMPL 
method DivMod(a: int, b: int) returns (q: int, r: int)
requires b != 0
ensures a == q * b + r
ensures 0 <= r < if b > 0 then b else -b
{
    if b > 0 {
        q := a / b;
        r := a % b;
    } else {
        /* code modified by LLM (iteration 1): Fixed division logic for negative b to ensure postcondition a == q * b + r holds */
        q := a / b;
        r := a % b;
        if r < 0 {
            q := q - 1;
            r := r - b;
        }
    }
}

/*
  triple Hoare (| P |) S (| Q |) 
*/