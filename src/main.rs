use ternary::T6;

fn main() {
    for i in T6::MIN_I64..=T6::MAX_I64 {
        let tryte = T6::try_from_int(i).unwrap();
        println!("table[index6({tryte})] = {i};");
    }
}
