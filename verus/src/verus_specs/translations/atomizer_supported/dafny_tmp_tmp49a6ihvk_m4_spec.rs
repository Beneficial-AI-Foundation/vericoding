#[derive(PartialEq, Eq)]
pub enum Color {
    Red,
    White,
    Blue,
}

pub open spec fn below(c: Color, d: Color) -> bool {
    c == Color::Red || c == d || d == Color::Blue
}

pub fn dutch_flag(a: &mut Vec<Color>)
    requires old(a).len() > 0,
    ensures forall|i: int, j: int| 0 <= i < j < a.len() ==> below(a[i], a[j]),
    ensures a@.to_multiset() == old(a)@.to_multiset(),
{
}