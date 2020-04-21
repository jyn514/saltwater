fn main() {
    write_git_version();
}
fn write_git_version() {
    let tag = git(&["describe", "--exact-match", "--tags", "HEAD"]);
    let version = tag.unwrap_or_else(|| {
        let commit = git(&["rev-parse", "--short=7", "HEAD"]).unwrap_or_else(|| "????".into());
        let most_recent_tag = match git(&["describe", "--tags", "--abbrev=0", "HEAD"]) {
            Some(c) => c,
            None => return std::env::var("CARGO_PKG_VERSION").unwrap(),
        };
        format!("{}-dev ({})", most_recent_tag, commit)
    });
    println!("cargo:rustc-env=RCC_GIT_REV={}", version);
    println!("cargo:rerun-if-changed=.git/HEAD");
}

fn git(args: &[&str]) -> Option<String> {
    use std::process::Command;
    let output = Command::new("git")
        .args(args)
        .output()
        .expect("failed to run `git`, is it installed?");
    if output.status.success() {
        Some(
            String::from_utf8(output.stdout)
                .expect("stdout was not valid utf8")
                .trim()
                .to_string(),
        )
    } else {
        use std::io::Write;

        let stdout = std::io::stdout();
        let mut stdout = stdout.lock();
        println!("failed to run `git {}`", args.join(" "));
        write!(stdout, "stdout: ").unwrap();
        stdout.write_all(&output.stdout).unwrap();
        write!(stdout, "stderr: ").unwrap();
        stdout.write_all(&output.stderr).unwrap();
        None
    }
}
