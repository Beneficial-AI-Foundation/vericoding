use vstd::prelude::*;

verus! {

fn center(input: Vec<Vec<char>>, width: usize) -> (res: Vec<Vec<char>>)
    requires
        width > 0,
        forall|i: int| 0 <= i < input.len() ==> #[trigger] input[i].len() >= 1,
    ensures
        res.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> 
            if #[trigger] input[i].len() > width as int { 
                res[i].len() == input[i].len() 
            } else { 
                res[i].len() == width as int 
            },
        forall|i: int| 0 <= i < input.len() ==> 
            if input[i].len() < width as int { 
                res[i]@.subrange(((width as int - input[i].len() + 1) / 2), ((width as int - input[i].len() + 1) / 2 + input[i].len())) == input[i]@
            } else { 
                true 
            },
{
    let mut res: Vec<Vec<char>> = Vec::new();
    
    for i in 0..input.len() {
        if input[i].len() >= width as int {
            res.push(input[i].clone());
        } else {
            let input_len = input[i].len() as usize;
            let padding = width - input_len;
            let left_pad = (padding + 1) / 2;
            let right_pad = padding - left_pad;
            
            let mut centered: Vec<char> = Vec::new();
            
            // Add left padding
            for _ in 0..left_pad {
                centered.push(' ');
            }
            
            // Add original string
            for j in 0..input_len {
                centered.push(input[i][j]);
            }
            
            // Add right padding  
            for _ in 0..right_pad {
                centered.push(' ');
            }
            
            res.push(centered);
        }
    }
    
    res
}

fn main() {}

}