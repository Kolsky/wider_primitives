use cfg_aliases::cfg_aliases;

fn main() {
    cfg_aliases! {
        hide_internal: { not(feature = "internals-doc-visible") },
        unstable: { feature = "unstable" },
        stable: { not(unstable) },
        debug: { debug_assertions },
        release: { not(debug_assertions) },
        serde: { feature = "serde" },
    }
}