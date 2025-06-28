use builtin::*;
use builtin_macros::*;

verus! {

#[derive(PartialEq, Eq)]
enum Color {
    Red,
    Blue,
    Green,
}

impl Color {
    spec fn len(self) -> Color {
        match self {
            Color::Red => Color::Red,
            Color::Blue => Color::Blue,
            Color::Green => Color::Green,
        }
    }
}

spec fn Below(c: Color, d: Color) -> bool {
    c == Color::Red || c == d.len() || d == Color::Blue
}

fn main() {
}

}