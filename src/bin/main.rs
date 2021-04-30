use anyhow::{bail, Context};

use hyperfr::{Granule, GRANULE_16K, GRANULE_4K};
use log::error;

fn main_granule<G: Granule + 'static>(granule: G) -> anyhow::Result<()> {
    let mut vmb = hyperfr::HfVmBuilder::new(granule).context("error creating HfVmBuilder")?;
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

fn main_result() -> anyhow::Result<()> {
    pretty_env_logger::init();

    match std::env::var("GRANULE").as_deref().unwrap_or_default() {
        "" | "16" => main_granule(GRANULE_16K),
        "4" => main_granule(GRANULE_4K),
        other => bail!("granule {} not recognized", other),
    }
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
