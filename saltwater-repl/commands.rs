use crate::repl::Repl;
use std::collections::HashMap;

pub fn default_commands() -> HashMap<&'static str, fn(&mut Repl, &str)> {
    let mut map = HashMap::<&'static str, fn(&mut Repl, &str)>::new();
    map.insert("help", help_command);
    map.insert("h", help_command);
    map.insert("quit", quit_command);
    map.insert("q", quit_command);
    map
}

fn help_command(_repl: &mut Repl, _args: &str) {
    print!(
        "\
Available commands:
    {p}help|h    Shows this message
    {p}quit|q    Quits the repl
",
        p = crate::repl::PREFIX
    );
}

fn quit_command(repl: &mut Repl, _args: &str) {
    repl.save_history();
    std::process::exit(0)
}
