fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b { a + b } else { u16::MAX }
}
fn main() {
    println!("sat_add(32768, 32768) = {}", sat_add(32768, 32768));
}
