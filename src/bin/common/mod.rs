#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ColorChoice {
    Always,
    Auto,
    Never,
}

impl ColorChoice {
    pub(super) fn use_color_for(self, stream: atty::Stream) -> bool {
        match self {
            ColorChoice::Always => true,
            ColorChoice::Never => false,
            ColorChoice::Auto => atty::is(stream),
        }
    }
}

impl std::str::FromStr for ColorChoice {
    type Err = &'static str;
    fn from_str(s: &str) -> Result<ColorChoice, &'static str> {
        match s {
            "always" => Ok(ColorChoice::Always),
            "auto" => Ok(ColorChoice::Auto),
            "never" => Ok(ColorChoice::Never),
            _ => Err("Invalid color choice"),
        }
    }
}

#[cfg(feature = "color-backtrace")]
pub(super) mod backtrace {
    use super::ColorChoice;
    use color_backtrace::termcolor::{self, StandardStream};
    use color_backtrace::BacktracePrinter;

    impl Into<termcolor::ColorChoice> for ColorChoice {
        fn into(self) -> termcolor::ColorChoice {
            match self {
                ColorChoice::Always => termcolor::ColorChoice::Always,
                ColorChoice::Auto => termcolor::ColorChoice::Auto,
                ColorChoice::Never => termcolor::ColorChoice::Never,
            }
        }
    }

    pub(crate) fn install(color: ColorChoice) {
        BacktracePrinter::new().install(Box::new(StandardStream::stderr(color.into())));
    }
}
