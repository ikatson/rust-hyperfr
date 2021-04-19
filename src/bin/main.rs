use anyhow::Context;

fn main() -> anyhow::Result<()> {
    pretty_env_logger::init();

    let mut vm = hyperfr::HfVm::new().context("error creating HfVm")?;
    let mut args = std::env::args_os();
    let image = args
        .nth(1)
        .context("first argument missing, required filename of the ELF image of the kernel")?;

    vm.load_elf(&image)
        .with_context(|| format!("error loading ELF image from filename {:?}", &image))?;
    let join = vm
        .vcpu_create_and_run(None)
        .context("error creating and running vcpu")?;
    join.join().unwrap()?;
    Ok(())
}
