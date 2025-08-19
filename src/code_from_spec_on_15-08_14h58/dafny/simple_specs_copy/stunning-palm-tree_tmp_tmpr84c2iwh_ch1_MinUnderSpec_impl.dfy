//IMPL 

// Ex 1.6
method MinUnderSpec (x: int, y: int) returns (r: int)
 ensures r <= x && r <= y {
    if x <= y {
        r := x;
    } else {
        r := y;
    }
}