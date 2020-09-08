use crate::repl::Repl;
use std::fmt::Write;

macro_rules! cmds {
    ($($($name:expr),* ; $description:expr => $action:expr),*$(,)?) => {{
        let mut cmds = Vec::new();
        $(
            cmds.push(Command { names: &[$($name),*], description: $description, action: $action });
        )*
        cmds
    }};
}

pub struct Command {
    pub names: &'static [&'static str],
    pub description: &'static str,
    pub action: fn(&mut Repl, &str),
}

pub fn default_commands() -> Vec<Command> {
    cmds! {
        "help", "h"; "Shows this help message" => help_command,
        "quit", "q"; "Quits the repl" => quit_command,
    }
}

pub fn generate_help_message(cmds: &[Command]) -> String {
    let inner = || {
        let mut buf = String::new();
        writeln!(buf, "Available commands:")?;
        for cmd in cmds {
            let names = cmd.names.iter().copied().collect::<Vec<_>>().join("|");
            writeln!(
                buf,
                "{:>4}{}{:>4}{}",
                crate::repl::PREFIX,
                names,
                "",
                cmd.description
            )?;
        }
        Ok::<String, Box<dyn std::error::Error>>(buf)
    };
    inner().expect("failed to generate help message")
}

fn help_command(repl: &mut Repl, _args: &str) {
    print!("{}", repl.help_message);
}

fn quit_command(repl: &mut Repl, _args: &str) {
    repl.save_history();
    std::process::exit(0)
}
