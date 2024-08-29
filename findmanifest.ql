import java
import codeql.xml.Xml

class AndroidManifestFile extends File {
  AndroidManifestFile() {
    this.getBaseName() = "AndroidManifest.xml"
  }
}

predicate isExported(XmlElement component) {
  component.getAttributeValue("android:exported") = "true"
  or
  (
    not exists(component.getAttributeValue("android:exported")) and
    exists(XmlElement intentFilter |
      intentFilter = component.getAChild() and
      intentFilter.getName() = "intent-filter"
    )
  )
}

predicate isValidComponent(XmlElement component) {
  component.getName() in ["activity", "service", "receiver", "provider"]
}

from AndroidManifestFile manifest, XmlElement manifestRoot, XmlElement application, XmlElement component
where
  manifestRoot.getFile() = manifest and
  manifestRoot.getName() = "manifest" and
  application = manifestRoot.getAChild() and
  application.getName() = "application" and
  component = application.getAChild()+ and
  component.getParent() = application and
  isValidComponent(component) and
  isExported(component)
select
  manifest.getAbsolutePath() as manifestPath,
  component.getName() as componentType,
  component.getAttributeValue("android:name") as componentName,
  "Exported component found in AndroidManifest.xml" as description