use anyhow::Context;

use log::error;

fn main_result() -> anyhow::Result<()> {
    pretty_env_logger::init();

    let mut vmb = hyperfr::HfVmBuilder::new().context("error creating HfVmBuilder")?;
    let mut args = std::env::args_os();
    let image = args
        .nth(1)
        .context("first argument missing, required filename of the ELF image of the kernel")?;

    vmb.load_elf(&image)
        .with_context(|| format!("error loading ELF image from filename {:?}", &image))?;
    let vm = vmb.build().context("error running HfVmBuilder.build()")?;
    let join = vm
        .vcpu_create_and_run(None)
        .context("error creating and running vcpu")?;
    join.join()
        .unwrap()
        .context("error in the thread running vcpu")?;
    Ok(())
}

fn main() {
    match main_result() {
        Ok(_) => {}
        Err(err) => {
            error!("Error running the hypervisor: {:?}", err);
            std::process::exit(1);
        }
    };
}
