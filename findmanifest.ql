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
  ", Root element: " + manifest.getRoot().getName()