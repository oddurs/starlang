use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::thread;
use std::time::Duration;

use crate::engine::StarEngine;
use crate::lens::SpokeId;
use crate::samples::SAMPLES;

fn fnv1a_hash(s: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

pub fn watch_directory(dir: &Path, stem: &str) -> Result<(), String> {
    fs::create_dir_all(dir).map_err(|e| format!("failed to create {}: {}", dir.display(), e))?;

    let paths: Vec<(SpokeId, PathBuf)> = SpokeId::ALL
        .iter()
        .map(|s| (*s, dir.join(format!("{}.{}", stem, s.extension()))))
        .collect();

    // Seed from an existing file if present, otherwise initialize from the default preset
    let mut engine = None;
    for (spoke, path) in &paths {
        if let Ok(existing) = fs::read_to_string(path) {
            if !existing.trim().is_empty() {
                let eng = StarEngine::from_source(*spoke, &existing)
                    .map_err(|d| format!("failed to parse existing {}: {}", path.display(), d))?;
                println!("Seeded Hub from existing {}", path.display());
                engine = Some(eng);
                break;
            }
        }
    }

    let mut engine = match engine {
        Some(e) => e,
        None => {
            let sample = &SAMPLES[0];
            StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?
        }
    };

    let mut last_hashes: HashMap<SpokeId, u64> = HashMap::new();
    let mut last_error_hashes: HashMap<SpokeId, u64> = HashMap::new();

    for (spoke, path) in &paths {
        let rendered = engine.project(*spoke);
        fs::write(path, &rendered)
            .map_err(|e| format!("failed writing {}: {}", path.display(), e))?;
        last_hashes.insert(*spoke, fnv1a_hash(&rendered));
    }

    println!("Star Compiler watching {} spokes in {}:", paths.len(), dir.display());
    for (spoke, path) in &paths {
        println!("  - {:<12} {}", spoke.display_name(), path.display());
    }
    println!("Edit and save ANY file above — the other 6 will update automatically. (Ctrl+C to stop)\n");

    loop {
        thread::sleep(Duration::from_millis(180));

        for (spoke, path) in &paths {
            let Ok(content) = fs::read_to_string(path) else {
                continue;
            };
            if content.trim().is_empty() {
                continue;
            }
            let h = fnv1a_hash(&content);
            if last_hashes.get(spoke) == Some(&h) {
                continue;
            }
            if last_error_hashes.get(spoke) == Some(&h) {
                continue;
            }

            match engine.apply_edit(*spoke, &content) {
                Ok(snap) => {
                    last_error_hashes.remove(spoke);
                    last_hashes.insert(*spoke, h);

                    // Project and write all OTHER spokes (plus normalize edited spoke if needed)
                    for (target_spoke, target_path) in &paths {
                        if *target_spoke == *spoke {
                            continue;
                        }
                        if let Some(code) = snap.views.get(target_spoke.as_str()) {
                            let target_hash = fnv1a_hash(code);
                            if last_hashes.get(target_spoke) != Some(&target_hash) {
                                if let Err(e) = fs::write(target_path, code) {
                                    eprintln!("Write error ({}): {}", target_path.display(), e);
                                } else {
                                    last_hashes.insert(*target_spoke, target_hash);
                                }
                            }
                        }
                    }

                    println!(
                        "[rev {}] Synced edit from {} -> updated other 6 spokes ({} Hub nodes)",
                        snap.revision,
                        spoke.display_name(),
                        snap.node_count
                    );
                    break;
                }
                Err(diag) => {
                    last_error_hashes.insert(*spoke, h);
                    eprintln!("Hold sync ({}): {}", path.file_name().unwrap().to_string_lossy(), diag);
                }
            }
        }
    }
}
