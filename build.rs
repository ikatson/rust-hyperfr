// Example custom build script.
fn main() {
    println!("cargo:rustc-link-lib=framework=Hypervisor");
}
