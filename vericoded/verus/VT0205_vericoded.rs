// <vc-preamble>
use vstd::prelude::*;

verus! {

struct FileHandle {

    path: String,

    is_binary: bool,

    position: nat,
}

enum DType {

    Float32,

    Float64,

    Int32,

    Int64,

    UInt8,
}

spec fn dtype_size_bytes(dtype: DType) -> nat {
    match dtype {
        DType::Float32 => 4,
        DType::Float64 => 8,
        DType::Int32 => 4,
        DType::Int64 => 8,
        DType::UInt8 => 1,
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_i8_cast_to_usize_equiv(x: i8)
    requires
        x >= 0,
    ensures
        (x as usize) == ((x as int) as usize),
{
}

// </vc-helpers>

// <vc-spec>
fn fromfile(file: FileHandle, dtype: DType, count: i8, sep: &str, offset: u8) -> (result: Vec<i8>)
    requires
        count == -1 || count > 0,
        sep == "" ==> file.is_binary == true,
        file.is_binary == true ==> sep == "",
    ensures
        count > 0 ==> result.len() == count as int as usize,

        file.is_binary == true ==> (
            #[trigger] (result@.len() * dtype_size_bytes(dtype))
            >= 0
        ),

        true,

        true,
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i8> = Vec::new();
    if count > 0 {
        proof { lemma_i8_cast_to_usize_equiv(count); }
        let n: usize = count as usize;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                result.len() == i,
                n == count as usize,
            decreases n - i
        {
            result.push(0i8);
            i = i + 1;
        }
        assert(result.len() == count as int as usize);
    }
    result
}
// </vc-code>

}
fn main() {}