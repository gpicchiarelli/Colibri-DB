import Foundation

@inline(__always)
func logDebug(_ message: String) {
	#if DEBUG
	print("[DEBUG] \(message)")
	#endif
}

@inline(__always)
func logInfo(_ message: String) {
	print("[INFO] \(message)")
}

@inline(__always)
func logWarning(_ message: String) {
	print("[WARN] \(message)")
}

@inline(__always)
func logError(_ message: String) {
	fputs("[ERROR] \(message)\n", stderr)
}
