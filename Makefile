.PHONY: bindgen
bindgen:
	bindgen \
        './bindgen.h' \
		--verbose \
        --raw-line 'use objc::*;' \
        --generate-block \
		-- \
		-I./fake-include/ \
        -x objective-c > src/bindgen.rs