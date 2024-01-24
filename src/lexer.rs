pub(crate) fn find_line_break(text: &str) -> usize {
    let line_break = text
        .bytes()
        .enumerate()
        .find_map(|(line, byte)| [b'\n', b'\r'].contains(&byte).then_some(line))
        .unwrap_or(text.len());

    match text.as_bytes().get(line_break + 1) {
        Some(b'\n') => line_break + 1,
        _ => line_break,
    }
}

pub(crate) fn lex_quoted(mut after_quote: &str, quote: char) -> Option<&str> {
    loop {
        after_quote = after_quote.trim_start_matches(|c: char| c != quote && c != '\\');
        if let Some(end) = after_quote.strip_prefix(quote) {
            break Some(end);
        }
        after_quote = match after_quote
            .trim_start_matches(|c: char| c != '\\')
            .strip_prefix(|_| true)
        {
            Some(after_escape) => after_escape,
            None => return None,
        };
    }
}

pub(crate) fn lex_raw_string(after_r: &str) -> Option<&str> {
    let after_pound = after_r.trim_matches('#');
    let start_pounds = &after_r[0..(after_r.len() - after_pound.len())];
    let mut after_quote = after_pound.strip_prefix('"').unwrap_or(after_pound);
    loop {
        after_quote = after_quote.trim_start_matches(|c: char| c != '"');
        if let Some(end_pounds) = after_quote.strip_prefix('"') {
            if let Some(end) = end_pounds.strip_prefix(start_pounds) {
                break Some(end);
            }
            after_quote = end_pounds;
        } else {
            break None;
        }
    }
}
