import java
import codeql.xml.Xml

class AndroidManifestFile extends File {
  AndroidManifestFile() {
    this.getAbsolutePath().matches("%/AndroidManifest.xml")
  }
}

from AndroidManifestFile manifest, XmlElement application, XmlElement component, string componentNameAttr
where
  manifest.getAbsolutePath() = application.getFile().getAbsolutePath() and
  application.getName() = "application" and
  component = application.getAChild() and
  component.getName() in ["activity", "service", "receiver", "provider"] and
  componentNameAttr = component.getAttributeValue("android:name")
select
  manifest.getAbsolutePath() as manifestPath,
  component.getName() as componentType,
  componentNameAttr as componentName,
  "Component found in AndroidManifest.xml" as description