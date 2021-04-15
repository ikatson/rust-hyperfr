.PHONY: bindgen
bindgen:
	bindgen \
        './bindgen.h' \
		--verbose \
        --raw-line 'use objc::*;' \
		-- \
		-I./fake-include/ \
        -x objective-c > src/bindgen.rs

.PHONY: run
run:
	cargo build
	codesign --entitlements vz.entitlements -s - target/debug/main
	target/debug/main /Users/igor/projects/2021-04-os-hypervisor-framework/armos/target/release/image.bin


.PHONY: test
test:
	# This builds, codesigns and runs the test binary
	cargo test --no-run && \
		FILENAME=$$(/opt/homebrew/opt/findutils/libexec/gnubin/find target/debug/deps -maxdepth 1 -type f -name 'hyperfr-*' -type f -printf "%T@ %Tc %p\n" | grep -v '\.d$$' | sort -n | tail -n 1 | awk '{print $$NF}') && \
		echo "$${FILENAME}" && \
		codesign --entitlements vz.entitlements -s - $${FILENAME} && \
		$${FILENAME}