use super::*;
use rustc_errors::{
    Applicability, CodeSuggestion, MultiSpan, Style, Subdiag, Substitution, SubstitutionPart,
};
use rustc_span::BytePos;
use rustc_span::source_map::FilePathMapping;

#[test]
fn diagnostic_details_preserve_primary_errors_and_suggestion_boundaries() {
    rustc_span::create_default_session_globals_then(|| {
        #[allow(
            clippy::arc_with_non_send_sync,
            reason = "the compiler emitter supplies SourceMap through Arc even in a single-threaded session"
        )]
        let source_map = Arc::new(SourceMap::new(FilePathMapping::empty()));
        let input_name = FileName::Real(
            source_map
                .path_mapping()
                .to_real_filename(&RealFileName::empty(), Path::new("input.rs")),
        );
        let input = source_map.new_source_file(input_name.clone(), "0123456789".to_owned());
        let other = source_map.new_source_file(
            FileName::Real(
                source_map
                    .path_mapping()
                    .to_real_filename(&RealFileName::empty(), Path::new("other.rs")),
            ),
            "other".to_owned(),
        );
        let span = |start, end| {
            Span::with_root_ctxt(
                input.start_pos + BytePos(start),
                input.start_pos + BytePos(end),
            )
        };
        let diagnostics = Arc::new(Mutex::new(DiagnosticState::default()));
        let mut emitter = CapturingEmitter {
            source_map,
            input_name,
            diagnostics: Arc::clone(&diagnostics),
        };
        let mut error = DiagInner::new(Level::Error, "primary error");
        error.code = Some(rustc_errors::E0308);
        error.span = MultiSpan::from_span(span(7, 8));
        error.span.push_span_label(span(0, 1), "earlier label");
        error.span.push_span_label(span(1, 2), "");
        error.span.push_span_label(
            Span::with_root_ctxt(other.start_pos, other.start_pos + BytePos(1)),
            "external label",
        );
        let mut child_span = MultiSpan::from_span(span(2, 3));
        child_span.push_span_label(span(3, 4), "bound label");
        error.children.push(Subdiag {
            level: Level::Note,
            messages: vec![("bound declared here".into(), Style::NoStyle)],
            span: child_span,
        });
        let suggestion =
            |message: &'static str, style, candidates: Vec<Vec<Span>>| CodeSuggestion {
                msg: message.into(),
                style,
                applicability: Applicability::MachineApplicable,
                substitutions: candidates
                    .into_iter()
                    .map(|parts| Substitution {
                        parts: parts
                            .into_iter()
                            .map(|span| SubstitutionPart {
                                span,
                                snippet: "replacement must not become a standalone patch".into(),
                            })
                            .collect(),
                    })
                    .collect(),
            };
        error.suggestions = Suggestions::Enabled(vec![
            suggestion(
                "single location",
                SuggestionStyle::ShowCode,
                vec![vec![span(4, 4)]],
            ),
            suggestion(
                "alternative candidates",
                SuggestionStyle::ShowCode,
                vec![vec![span(4, 5)], vec![span(5, 6)]],
            ),
            suggestion(
                "combined edits",
                SuggestionStyle::ShowAlways,
                vec![vec![span(4, 5), span(5, 6)]],
            ),
            suggestion(
                "explanation only",
                SuggestionStyle::HideCodeAlways,
                vec![vec![span(6, 7)]],
            ),
            suggestion(
                "tool only",
                SuggestionStyle::CompletelyHidden,
                vec![vec![span(6, 7)]],
            ),
        ]);
        emitter.emit_diagnostic(error);
        let mut second = DiagInner::new(Level::Error, "second error");
        second.span = MultiSpan::from_span(span(8, 9));
        emitter.emit_diagnostic(second);
        emitter.emit_diagnostic(DiagInner::new(Level::Warning, "unrelated warning"));

        let diagnostics = diagnostics.lock().unwrap();
        assert_eq!(diagnostics.errors.len(), 2);
        let first = &diagnostics.errors[0];
        assert_eq!(first.code, Some(rustc_errors::E0308));
        assert_eq!(
            first.primary.normalized_range,
            Some(ByteRange { start: 7, end: 8 })
        );
        assert_eq!(first.primary.message, "primary error");
        assert!(!first.compiler_bug);
        assert_eq!(first.related.len(), 8);
        for (message, level, range) in [
            ("earlier label", DiagnosticLevel::Note, Some((0, 1))),
            ("external label", DiagnosticLevel::Note, None),
            ("bound declared here", DiagnosticLevel::Note, Some((2, 3))),
            ("bound label", DiagnosticLevel::Note, Some((3, 4))),
            ("single location", DiagnosticLevel::Help, Some((4, 4))),
            ("alternative candidates", DiagnosticLevel::Help, None),
            ("combined edits", DiagnosticLevel::Help, None),
            ("explanation only", DiagnosticLevel::Help, Some((6, 7))),
        ] {
            let detail = first
                .related
                .iter()
                .find(|detail| detail.message == message)
                .unwrap();
            assert_eq!(detail.level, level);
            assert_eq!(
                detail.normalized_range,
                range.map(|(start, end)| ByteRange { start, end })
            );
        }
        assert_eq!(
            diagnostics.errors[1].primary.normalized_range,
            Some(ByteRange { start: 8, end: 9 })
        );
    });
}
