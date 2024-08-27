import java
import codeql.xml.Xml

class AndroidManifestFile extends XmlFile {
  AndroidManifestFile() {
    this.getBaseName() = "AndroidManifest.xml"
  }
}

from AndroidManifestFile manifest
select manifest,
  "AndroidManifest.xml found at path: " + manifest.getAbsolutePath() + 
  ", File size: " + manifest.getSize().toString() + " bytes" +
  ", Last modified: " + manifest.getLastModified().toString()